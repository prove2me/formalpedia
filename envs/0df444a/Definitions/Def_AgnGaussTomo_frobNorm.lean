-- Prove2me | Definitions.Def_AgnGaussTomo_frobNorm
-- name    : AgnGaussTomo_frobNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:21.04235+00:00
-- url     : https://prove2.me/theorems/5cfe639a-95db-4c92-bbcb-3533158fe074
-- title:
--   Frobenius norm $\|M\|_F$
-- statement:
--   For a real or complex matrix $M$, $\|M\|_F=\big(\sum_{i,j}|M_{ij}|^2\big)^{1/2}$.
--
--   It measures the covariance error in Lemma 3.7 and enters the norm $\|(b,A)\|_{\mathcal P}^2=\|b\|_2^2+\tfrac12\|A\|_F^2$ of Bargmann parameters (Eq. (12)).
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Eq. (12), printed p. 12 (PDF p. 15); Lemma 3.7, Eq. (20), p. 17 (PDF p. 20)

import Mathlib

namespace AgnGaussTomo

/-- **Frobenius norm `‖M‖_F = (Σᵢⱼ |Mᵢⱼ|²)^{1/2}`.** Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian
Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), Eq. (12), printed p. 12
(`‖(b, A)‖²_P = ‖b‖²₂ + ½‖A‖²_F`) and Lemma 3.7, Eq. (20), p. 17 (`‖Σ̂_h − Σ_h‖_F ≤ ζ`). -/
noncomputable def frobNorm {𝕜 : Type} [RCLike 𝕜] {ι κ : Type} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ 𝕜) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2)

end AgnGaussTomo


