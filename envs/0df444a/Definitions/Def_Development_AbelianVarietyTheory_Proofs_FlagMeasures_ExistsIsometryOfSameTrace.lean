-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:05:31.15819+00:00
-- url     : https://prove2.me/theorems/8d895b46-7dac-589c-be0f-93ae7a7075d3
-- title:
--   Exists Isometry Of Same Trace
-- statement:
--   Definitions and structural lemmas for Exists Isometry Of Same Trace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryOfSameTrace.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgebraMapMemO
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_l
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.SameTrace
open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
theorem hf_zero_l (y : Fin n → E) : hf L Hm 0 y = 0 := by simp [hf]
theorem hf_sum_l {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L Hm (a i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_l]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, ih]
noncomputable def shear {m : ℕ} (b d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0) :
    (Fin n → E) ≃ₗ[E] (Fin n → E) where
  toFun v := v + ∑ j, hf L Hm v (b j) • d j
  map_add' v w := by simp only [hf_add_l, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c v := by
    simp only [hf_smul_l, RingHom.id_apply, smul_add, Finset.smul_sum, mul_smul]
  invFun v := v - ∑ j, hf L Hm v (b j) • d j
  left_inv v := by simp [hf_add_l, hf_sum_l, hf_smul_l, hdb]
  right_inv v := by simp [hf_sub_l, hf_sum_l, hf_smul_l, hdb]
end
end GlobalTheory.HL.SameTrace


