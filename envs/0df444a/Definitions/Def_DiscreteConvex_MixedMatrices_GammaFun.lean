-- Prove2me | Definitions.Def_DiscreteConvex_MixedMatrices_GammaFun
-- name    : DiscreteConvex_MixedMatrices_GammaFun
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:37:45.194987+00:00
-- url     : https://prove2.me/theorems/f6f52fdf-a9cf-4b09-ade6-f3cfe1ab7e00
-- title:
--   Nonzero-row count $\gamma(I,J)$
-- statement:
--   $\gamma(I,J) = |\{i \in I \mid \exists j \in J,\ T_{ij} \ne 0\}|$: the number of nonzero rows of the submatrix $T[I,J]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.357.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.357

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.357: the function γ counting the nonzero rows of
a submatrix of `T`, in `DiscreteConvex.MixedMatrices`.
-/

namespace DiscreteConvex.MixedMatrices

open Classical in
/-- `γ(I,J) = |{i ∈ I | ∃ j ∈ J, Tᵢⱼ ≠ 0}|`: the number of nonzero rows of the submatrix
`T[I,J]`. -/
noncomputable def GammaFun {R C F : Type*} [Zero F] (T : Matrix R C F) (I : Finset R)
    (J : Finset C) : ℕ :=
  (I.filter (fun i => ∃ j ∈ J, T i j ≠ 0)).card

end DiscreteConvex.MixedMatrices


