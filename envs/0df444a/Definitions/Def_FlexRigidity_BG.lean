-- Prove2me | Definitions.Def_FlexRigidity_BG
-- name    : FlexRigidity_BG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:20:15.553343+00:00
-- url     : https://prove2.me/theorems/4a3d5cb6-a816-4814-b8c6-b97edab84be9
-- title:
--   The function $B_{\mathsf G}$, eq. (64)
-- statement:
--   $B_{\mathsf G}(\delta)=\min\{1,\mathrm{van}_{\mathsf G}(\delta)^2\}$ for $\delta\in[0,\omega^*]$ and $\min\{1,\mathrm{van}_{\mathsf G}(\omega^*)^2\}$ for $\delta\in(\omega^*,1]$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (64), p. 53

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The function `B_G`, eq. (64)** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444,
artifact sha256 8c67699d…, p. 53): `B_G(δ) = min{1, van_G(δ)²}` for `δ ∈ [0, ω*]` and
`min{1, van_G(ω*)²}` for `δ ∈ (ω*, 1]`; `ω` is `ω*`. -/
def BG (van : ℝ → ℝ) (ω δ : ℝ) : ℝ :=
  if δ ≤ ω then min 1 (van δ ^ 2) else min 1 (van ω ^ 2)

end FlexRigidity


