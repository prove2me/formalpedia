-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TraceEqSumLocalTracesAbovePrime
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_TraceEqSumLocalTracesAbovePrime
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:18:53.872273+00:00
-- url     : https://prove2.me/theorems/bb751939-6f73-417c-a7f2-5bf3016b867b
-- title:
--   Trace Eq Sum Local Traces Above Prime
-- statement:
--   Definitions and structural lemmas for Trace Eq Sum Local Traces Above Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
namespace GlobalTheory.LocalTraceSum
open Filter Topology TensorProduct
section Local
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {l : ℕ} [Fact l.Prime] [Algebra ℚ_[l] K]
variable {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]
end Local
section Place
variable {F : Type} [Field F] [NumberField F] {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω]
theorem norm_int_le (σ : F →+* Ω) (a : 𝓞 F) : ‖σ a‖ ≤ 1 := by
  have h : IsIntegral ℤ (σ a) := a.isIntegral_coe.map σ.toIntAlgHom
  have h2 : IsIntegral (NormedField.valuation (K := Ω)).integer (σ a) := h.tower_top
  have := (Valuation.integer.integers _).mem_of_integral h2
  exact this
def ker (σ : F →+* Ω) : Ideal (𝓞 F) where
  carrier := {a | ‖σ a‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, RingOfIntegers.coe_eq_algebraMap, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul] at *
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le σ c)) ha
end Place
section Ext
variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[l] K] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]
end Ext
end GlobalTheory.LocalTraceSum


