-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:06:44.902724+00:00
-- url     : https://prove2.me/theorems/2df22aa4-dc9e-4551-9c2d-978c845c2f22
-- title:
--   Eis Automorphy Linear
-- statement:
--   Definitions and structural lemmas for Eis Automorphy Linear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EisAutomorphyLinear.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubSmulOne
import Theorems.Thm_GlobalTheory_SW_EisBdd_botSpan_mul
import Theorems.Thm_GlobalTheory_SW_HAct_group_part
import Theorems.Thm_GlobalTheory_SW_HAct_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.EisTrans
variable {N : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n : ℕ}
omit [NumberField E] [IsCMField E] in

theorem botSpan_mul (g γ : M2 E N) : botSpan (g * γ) = (botSpan g).map γ.vecMulLinear := by
  unfold botSpan
  rw [Submodule.map_span, ← Set.range_comp]
  rfl
noncomputable def lagMul {γ : M2 E N} (hγ : γ ∈ UU E N) (U : Lag E N) : Lag E N :=
  ⟨U.1.map γ.vecMulLinear, U.2.choose * γ, HAct.mul_mem hγ U.2.choose_spec.1, by
    rw [botSpan_mul, U.2.choose_spec.2]⟩
theorem lagMul_lagMul {γ γ' : M2 E N} (hγ : γ ∈ UU E N) (hγ' : γ' ∈ UU E N) (h : γ * γ' = 1)
    (U : Lag E N) : lagMul hγ' (lagMul hγ U) = U := by
  apply Subtype.ext
  change (U.1.map γ.vecMulLinear).map γ'.vecMulLinear = U.1
  rw [← U.2.choose_spec.2, ← botSpan_mul, ← botSpan_mul, Matrix.mul_assoc, h, Matrix.mul_one]
noncomputable def lagEquiv {γ : M2 E N} (hγ : γ ∈ UU E N) : Lag E N ≃ Lag E N :=
  ⟨lagMul hγ, lagMul (HAct.group_part hγ).2.1,
    lagMul_lagMul _ _ (mul_nonsing_inv γ (HAct.group_part hγ).1),
    lagMul_lagMul _ _ (nonsing_inv_mul γ (HAct.group_part hγ).1)⟩
end GlobalTheory.SW.EisTrans


