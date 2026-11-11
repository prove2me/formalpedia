-- Prove2me | Definitions.Def_FlexRigidity_genFidelity
-- name    : FlexRigidity_genFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:16:26.271473+00:00
-- url     : https://prove2.me/theorems/eba95fe1-90af-4587-b069-d824285a0c6d
-- title:
--   Generalized fidelity $F(\rho,\sigma)$
-- statement:
--   For subnormalized states $\rho,\sigma$ the **generalized fidelity** is
--   $$F(\rho,\sigma)=\big\|\sqrt\rho\sqrt\sigma\big\|_1+\sqrt{(1-\operatorname{Tr}\rho)(1-\operatorname{Tr}\sigma)}.$$
--   It reduces to the usual fidelity for normalized states.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 2.6, p. 19

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_traceNorm
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Generalized fidelity** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact
sha256 8c67699d…, Definition 2.6, p. 19): for subnormalized `ρ, σ`,
`F(ρ, σ) = ‖√ρ √σ‖₁ + √((1 − Tr ρ)(1 − Tr σ))`. -/
def genFidelity {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Matrix I I ℂ) : ℝ :=
  traceNorm (spectralPower ρ (1 / 2) * spectralPower σ (1 / 2)) +
    Real.sqrt ((1 - tr ρ) * (1 - tr σ))

end FlexRigidity


