-- Prove2me | Definitions.Def_FlexRigidity_purifiedDist
-- name    : FlexRigidity_purifiedDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:24.229869+00:00
-- url     : https://prove2.me/theorems/33f912d4-fe15-4fb3-a682-f7e79271ba7b
-- title:
--   Purified distance $P(\rho,\sigma)$
-- statement:
--   For subnormalized states, the **purified distance** is $P(\rho,\sigma)=\sqrt{1-F(\rho,\sigma)^2}$ with the generalized fidelity $F$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 2.6, p. 19

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_genFidelity
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Purified distance** `P(ρ, σ) = √(1 − F(ρ, σ)²)` (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, Definition 2.6, p. 19), with the generalized fidelity
`F`. -/
def purifiedDist {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Matrix I I ℂ) : ℝ :=
  Real.sqrt (1 - genFidelity ρ σ ^ 2)

end FlexRigidity


