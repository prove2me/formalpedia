-- Prove2me | Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedPolyMatrix
-- name    : DiscreteConvex_MixedMatrices_IsMixedPolyMatrix
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:37:08.955761+00:00
-- url     : https://prove2.me/theorems/aa34ef61-bacb-45fb-8a5c-c0881de841ab
-- title:
--   Mixed polynomial matrix (Eq. 12.8)
-- statement:
--   $A(s) = Q(s) + T(s)$ (Eq. (12.8)) is a **mixed polynomial matrix** with respect to $(K,F)$: $Q(s)$ has all coefficients over $K$ (axiom (MP-Q)) embedded into $F[s]$ via `Polynomial.map`, $T(s)$ has coefficients over $F$ (axiom (MP-T)), and the family of *all* nonzero coefficients of *all* entries of $T(s)$ (indexed by row, column, and degree) is algebraically independent over $K$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.355, Eq. (12.8).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.355, Eq. (12.8)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.355, Eq. (12.8), axioms (MP-Q), (MP-T): the
definition of a mixed polynomial matrix, in `DiscreteConvex.MixedMatrices`.
-/

namespace DiscreteConvex.MixedMatrices

/-- `A(s) = Q(s) + T(s)` (Eq. (12.8)) is a **mixed polynomial matrix** with respect to `(K, F)`:
`Q(s)` has all coefficients over `K` (axiom (MP-Q)) embedded into `F[s]` via `Polynomial.map`,
`T(s)` has coefficients over `F` (axiom (MP-T)), and the family of all nonzero coefficients of all
entries of `T(s)` is algebraically independent over `K`. -/
def IsMixedPolyMatrix {R K F : Type*} [Fintype R] [Field K] [Field F] [Algebra K F]
    (A : Matrix R R (Polynomial F)) (Q : Matrix R R (Polynomial K)) (T : Matrix R R (Polynomial F)) :
    Prop :=
  (∀ i j, A i j = (Q i j).map (algebraMap K F) + T i j) ∧
  AlgebraicIndependent K
    (fun e : {p : R × R × ℕ // (T p.1 p.2.1).coeff p.2.2 ≠ 0} =>
      (T e.1.1 e.1.2.1).coeff e.1.2.2)

end DiscreteConvex.MixedMatrices


