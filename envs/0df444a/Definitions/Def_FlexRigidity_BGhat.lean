-- Prove2me | Definitions.Def_FlexRigidity_BGhat
-- name    : FlexRigidity_BGhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:56.786523+00:00
-- url     : https://prove2.me/theorems/2fec174c-9a01-4b06-aeee-3518de174f64
-- title:
--   The concave majorant $\hat B_{\mathsf G}$, eq. (65)
-- statement:
--   $\hat B_{\mathsf G}(\delta)=\sup\{\sum_j\lambda_jB_{\mathsf G}(\delta_j):\lambda_j\ge0,\ \delta_j\in[0,1],\ \sum_j\lambda_j=1,\ \sum_j\lambda_j\delta_j=\delta\}$, the supremum over all finite mixtures.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (65), p. 54

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_BG
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The concave majorant `B̂_G`, eq. (65)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 54):
`B̂_G(δ) = sup { Σ_j λ_j B_G(δ_j) : λ_j ≥ 0, δ_j ∈ [0, 1], Σ_j λ_j = 1, Σ_j λ_j δ_j = δ }`, the
supremum over all finite mixtures.

**Formalization Note** Real `sSup`; for `δ ∈ [0, 1]` the set is nonempty (the trivial mixture) and
bounded by `1`. -/
def BGhat (van : ℝ → ℝ) (ω δ : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (k : ℕ) (l d : Fin k → ℝ), (∀ j, 0 ≤ l j) ∧ (∀ j, d j ∈ Set.Icc (0 : ℝ) 1) ∧
    ∑ j, l j = 1 ∧ ∑ j, l j * d j = δ ∧ v = ∑ j, l j * BG van ω (d j)}

end FlexRigidity


