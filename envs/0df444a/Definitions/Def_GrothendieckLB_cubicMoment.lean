-- Prove2me | Definitions.Def_GrothendieckLB_cubicMoment
-- name    : GrothendieckLB_cubicMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:21.86761+00:00
-- url     : https://prove2.me/theorems/4d2d4517-25da-4518-81c8-dfee0a6ae685
-- title:
--   Degree-three Hermite moment $T_F(i,j,l)$
-- statement:
--   For $F:\mathbb R^d\to\mathbb R$ and coordinates $i,j,l$,
--   $$
--   T_F(i,j,l)=\mathbb E\big[F(X)\big(X_iX_jX_l-\delta_{ij}X_l-\delta_{il}X_j-\delta_{jl}X_i\big)\big].
--   $$
--   Up to the normalizing constants of the orthonormal Hermites, these are the coefficients of $F$ on the degree-three directions $\mathrm{He}_3(X_i)$, $\mathrm{He}_2(X_i)\mathrm{He}_1(X_j)$ and $\mathrm{He}_1(X_i)\mathrm{He}_1(X_j)\mathrm{He}_1(X_\ell)$ named on p.31.
--
--   **Formalization Note** This is the moment form used by the published `GrothendieckConstant.coeff_hermite_moments`.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31

import Mathlib
import Definitions.Def_GrothendieckLB_gaussExp

namespace GrothendieckLB

/-- The degree-three Hermite tensor entry
`T_F(i,j,l) = E[F(X)(X_i X_j X_l − δ_ij X_l − δ_il X_j − δ_jl X_i)]`
(Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31, in the moment form of `GrothendieckConstant.coeff_hermite_moments`). -/
noncomputable def cubicMoment {d : ℕ} (F : (Fin d → ℝ) → ℝ) (i j l : Fin d) : ℝ :=
  gaussExp fun x => F x * (x i * x j * x l - (if i = j then x l else 0)
    - (if i = l then x j else 0) - (if j = l then x i else 0))

end GrothendieckLB


