-- Prove2me | Definitions.Def_FlexRigidity_PC
-- name    : FlexRigidity_PC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:19:03.045788+00:00
-- url     : https://prove2.me/theorems/deefd314-b41d-4f73-ad18-f69202105ed9
-- title:
--   The ideal record distribution $P_C$
-- statement:
--   $P_C(\mathrm{gen})=1-\gamma$, $P_C(1)=\gamma\omega^*$, $P_C(0)=\gamma(1-\omega^*)$. With $\omega^*-\delta$ in place of $\omega^*$ it is the distribution $P^\delta_C$ of p. 54.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), p. 40; p. 54

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

/-- **The ideal record distribution `P_C`** of Protocol 2 (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 40): `P_C(gen) = 1 − γ`, `P_C(1) = γ ω*`,
`P_C(0) = γ(1 − ω*)`, on `C = {gen, 0, 1}` = `Option Bool` (`none` = gen). With `ω = ω* − δ` it is
the distribution `P^δ_C` of p. 54. -/
def PC (γ ω : ℝ) : Option Bool → ℝ
  | none => 1 - γ
  | some true => γ * ω
  | some false => γ * (1 - ω)

end FlexRigidity


