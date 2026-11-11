-- Prove2me | Definitions.Def_FlexRigidity_canonPurif
-- name    : FlexRigidity_canonPurif
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:11.736965+00:00
-- url     : https://prove2.me/theorems/cc60653b-bcdc-487f-9b2f-0420d2d5ba47
-- title:
--   Canonical purification
-- statement:
--   For a state $\rho_M$, $|\rho\rangle_{MR}=(\sqrt{\rho_M}\otimes I_R)\sum_x|x\rangle_M|x\rangle_R$ with $R\cong M$. Its marginal on $M$ is $\rho_M$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), proof of Lemma 3.4, p. 25

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

/-- **Canonical purification** `|ρ⟩_{MR} = (√ρ_M ⊗ I_R) Σ_x |x⟩_M |x⟩_R` (Arqand–Kundu–Tan,
*Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, proof of Lemma 3.4, p. 25), with
`R ≅ M` placed first: the vector with entries `(√ρ)_{m r}` at `(r, m)`. For a density matrix `ρ`
its marginal on `M` is `ρ`. -/
def canonPurif {M : Type} [Fintype M] [DecidableEq M] (ρ : Matrix M M ℂ) : M × M → ℂ :=
  fun p => spectralPower ρ (1 / 2) p.2 p.1

end FlexRigidity


