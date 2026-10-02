-- Prove2me | Definitions.Def_DiscreteConvex_MixedMatrices_SubDegDet
-- name    : DiscreteConvex_MixedMatrices_SubDegDet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:37:20.786973+00:00
-- url     : https://prove2.me/theorems/6c0e834b-1ca9-46ee-a1b3-72ddccba973d
-- title:
--   Degree of the determinant of a square submatrix
-- statement:
--   $\deg\det M[I,J]$ for a submatrix with $|I|=|J|$: reindex $M[I,J]$ to a genuinely square matrix over the common type $I$ via an (arbitrary) bijection $I \simeq J$, then take `Polynomial.degree` of its determinant.
--
--   **Formalization Note.** Changing the bijection only changes the determinant by a sign (a column permutation), so the degree — `⊥` exactly when the determinant is the zero polynomial, matching the book's convention $\deg\det = -\infty$ for a singular submatrix — does not depend on this choice. When $|I| \ne |J|$ (never the case where this is used in this mission), the value is `⊥` by convention.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.360, Theorem 12.13.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.360, Theorem 12.13

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.360, Theorem 12.13 (the quantities
`deg det Q[I,J]`, `deg det T[R\I,C\J]`): the degree of the determinant of a square submatrix of a
polynomial matrix, in `DiscreteConvex.MixedMatrices`.
-/

namespace DiscreteConvex.MixedMatrices

/-- `deg det M[I,J]` for `M : Matrix R C (Polynomial 𝔽)` and `I ⊆ R`, `J ⊆ C` with
`I.card = J.card`: reindex `M[I,J]` to a genuinely square matrix over the common type `I` via an
arbitrary bijection `I ≃ J` (given by `Fintype.equivOfCardEq`), then take `Polynomial.degree` of
its determinant. Changing the bijection only changes the determinant by a sign (a column
permutation), so the degree — `⊥` exactly when the determinant is the zero polynomial, matching
the book's convention `deg det = −∞` for a singular submatrix — does not depend on this choice.
When `I.card ≠ J.card` (never the case where this is used in this mission), the value is `⊥`. -/
noncomputable def SubDegDet {R C 𝔽 : Type*} [Fintype R] [Fintype C] [Field 𝔽] [DecidableEq R]
    (M : Matrix R C (Polynomial 𝔽)) (I : Finset R) (J : Finset C) : WithBot ℕ :=
  if h : Fintype.card I = Fintype.card J then
    (Matrix.det (fun a b : I => M (a : R) ((Fintype.equivOfCardEq h b : J) : C))).degree
  else ⊥

end DiscreteConvex.MixedMatrices


