-- Prove2me | Definitions.Def_GroupIsoPoly_Congruent
-- name    : GroupIsoPoly_Congruent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:52:11.642929+00:00
-- url     : https://prove2.me/theorems/2768956d-4b51-4fa0-b327-791a8f3ba1ea
-- title:
--   Congruence of matrix tuples
-- statement:
--   Two tuples $A=(A_1,\dots,A_m)$ and $B=(B_1,\dots,B_m)$ of $n\times n$ matrices over a field are **congruent** if there is $L\in\mathrm{GL}(n)$ with
--   $$
--   A_i=L\,B_i\,L^{t}\qquad\text{for every }i\in[m].
--   $$
--   This is Definition 10 (3) of the paper; the Matrix Tuple Congruence problem asks whether two tuples are congruent.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 10 (3), p.27 (PDF p.31); §1.3, p.2 (PDF p.6)

import Mathlib

set_option autoImplicit false

namespace GroupIsoPoly

/-- **Congruence of matrix tuples.**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 10 (3), p.27 (PDF p.31): "A and B are
congruent if there exists L ∈ GL(n, q), such that for any i ∈ [m], A_i = L B_i L^t."

`Congruent A B` for `A, B : Fin m → Matrix (Fin n) (Fin n) K` says that some invertible `L` has
`A_i = L B_i Lᵀ` for every `i`. -/
def Congruent {K : Type*} [CommRing K] {n m : ℕ} (A B : Fin m → Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ L : GL (Fin n) K, ∀ i, A i = (L : Matrix (Fin n) (Fin n) K) * B i *
    (L : Matrix (Fin n) (Fin n) K).transpose

end GroupIsoPoly


