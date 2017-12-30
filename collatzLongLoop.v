
Require Import Omega.

Axiom x_0 s a : nat.
Axiom multi : nat. (* multi = (1+1/3x_0)…(1+1/3x_3s-1) *)
Axiom exp :
  forall(x a b:nat),
    a<=b -> 100/2 < 100*((1+1/x)^x)^(a/b)/8 -> 100/2 < 272/8.
Axiom mu : 100*(1/2) < 100*(multi/8) -> 100/2 < 100*((1+1/(3*x_0))^(3*x_0))^(a*s/x_0)/8.
Axiom log2 : nat -> nat.
Axiom logOut :
  forall(x:nat),
    0-1 < log2 x -> 1/2 < x.
Axiom up : nat -> nat.
Axiom upOut :
  forall(a b:nat),
    up(a+b) - up(a) = 0 -> 0-1 < b.

(** upを外す *)
Lemma l1:
  up(log2(x_0*(3/2)^(3*a*s))+log2(multi/8)) - up(log2(x_0*(3/2)^(3*a*s))) = 0
    -> 0-1 < log2(multi/8).
Proof.
  apply upOut.
Qed.

(** logを外す *)
Lemma l2:
  0-1 < log2(multi/8) -> 1/2 < multi/8.
Proof.
  apply logOut.
Qed.

Lemma l3:
  (100/2 < 272/8) -> False.
Proof.
  intros.
  simpl in H.
  omega.
Qed.

(** [logX_3as'] - [logY_3as] = 0 と as <= x_0 から矛盾を導く *)
(** よって、s > x_0/a *)
Theorem collatzLongLoop :
  up(log2(x_0*(3/2)^(3*a*s))+log2(multi/8)) - up(log2(x_0*(3/2)^(3*a*s))) = 0
    -> a*s <= x_0
      -> False.
Proof.
  intros.
  apply l1 in H.
  apply l2 in H.
  apply (Nat.mul_lt_mono_pos_l 100 (1/2) (multi/8)) in H.
  apply mu in H.
  apply exp in H.
  apply l3 in H.
  auto.
  auto.
  omega.
Qed.
















