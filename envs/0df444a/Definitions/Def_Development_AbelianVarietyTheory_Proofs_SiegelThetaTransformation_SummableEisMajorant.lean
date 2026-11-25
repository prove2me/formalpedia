-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:17:52.517311+00:00
-- url     : https://prove2.me/theorems/238f35b4-d25a-4799-a74c-11b043b5a278
-- title:
--   Summable Eis Majorant
-- statement:
--   Definitions and structural lemmas for Summable Eis Majorant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot


set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.EisConv
noncomputable def embAll (E m : Type) [Field E] [NumberField E] :
    (m → 𝓞 E) →ₗ[ℤ] (m → (E →+* ℂ) → ℂ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun w j σ => σ (w j : E)
      map_zero' := by ext j σ; simp
      map_add' := fun s t => by ext j σ; simp }
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
end GlobalTheory.SW.EisConv


