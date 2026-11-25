-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSum
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSum
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:55:16.882447+00:00
-- url     : https://prove2.me/theorems/43d1bcff-f195-572a-b921-ba2595139964
-- title:
--   Hermitian Local Character Sum
-- statement:
--   Definitions and structural lemmas for Hermitian Local Character Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianLocalCharacterSum.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqNormSumRepsMulIndexLe
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open scoped Pointwise ENNReal Classical ComplexConjugate
namespace GlobalTheory.HL.DivisibleGauss
section Form
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
theorem form_add_left (a b y : Fin n → E) : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]
def formLeft (y : Fin n → E) : (Fin n → E) →+ E :=
  AddMonoidHom.mk' (fun x => hf L Hm x y) fun a b => form_add_left L Hm a b y
def divBy (U : Submodule L.O (Fin n → E)) {ρ : ℕ} (e : Fin ρ → Fin n → E) (x : E) :
    AddSubgroup (Fin n → E) where
  carrier := {u | u ∈ U ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = x * c}
  zero_mem' := ⟨U.zero_mem, fun a => ⟨0, L.O.zero_mem, by simp [hf]⟩⟩
  add_mem' := by
    rintro u w ⟨hu, hu'⟩ ⟨hw, hw'⟩
    refine ⟨U.add_mem hu hw, fun a => ?_⟩
    obtain ⟨c, hc, h⟩ := hu' a
    obtain ⟨d, hd, h'⟩ := hw' a
    exact ⟨c + d, L.O.add_mem hc hd, by rw [form_add_left, h, h', mul_add]⟩
  neg_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨U.neg_mem hu, fun a => ?_⟩
    obtain ⟨c, hc, h⟩ := hu' a
    refine ⟨-c, L.O.neg_mem hc, ?_⟩
    rw [mul_neg, ← h]
    exact map_neg (formLeft L Hm (e a)) u
end Form
end GlobalTheory.HL.DivisibleGauss


