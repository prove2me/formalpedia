-- Prove2me | Definitions.Def_FlexRigidity_roundDeficit
-- name    : FlexRigidity_roundDeficit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:24:58.31812+00:00
-- url     : https://prove2.me/theorems/4f6a9792-9b7c-47db-b423-511f16bcd508
-- title:
--   Deficit of the round strategy
-- statement:
--   For a normalized purified input $|\rho\rangle_{RM^{\mathrm A}_iM^{\mathrm B}_i}$, the deficit $\delta=\delta_{\mathsf G}(\mathfrak S)$ of the strategy $\mathfrak S=(\operatorname{Tr}_R|\rho\rangle\langle\rho|\otimes|0\rangle\langle0|_{M'^{\mathrm A}_i}\otimes|0\rangle\langle0|_{M'^{\mathrm B}_i},\{H^x_{i,a}\},\{K^y_{i,b}\})$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), §5.4, p. 47

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_deficit
import Definitions.Def_FlexRigidity_withAnc
import Definitions.Def_ObliviousRSP_pureState
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The deficit `δ` of the round strategy** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, §5.4, p. 47): for a normalized purified input
`|ρ⟩_{R M^A_i M^B_i}`, the strategy
`S = (Tr_R[|ρ⟩⟨ρ|] ⊗ |0⟩⟨0|_{M′^A_i} ⊗ |0⟩⟨0|_{M′^B_i}, {H^x_{i,a}}, {K^y_{i,b}})` and `δ = δ_G(S)`. -/
def roundDeficit {X Y A B R : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype R]
    (G : Game X Y A B) (I : StoredImpl X Y A B) (i : ℕ)
    (ρ : R × (Fin (I.dA i) × Fin (I.dB i)) → ℂ) : ℝ :=
  deficit G (rightMarginal (ObliviousRSP.pureState (withAnc I i ρ))) (I.H i) (I.K i)

end FlexRigidity


