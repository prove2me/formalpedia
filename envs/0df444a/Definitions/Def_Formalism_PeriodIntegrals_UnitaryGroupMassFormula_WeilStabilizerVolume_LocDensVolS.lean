-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolS
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolS
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:50:46.039606+00:00
-- url     : https://prove2.me/theorems/ea685b88-cc0c-4bc8-86cc-4b46a210b554
-- title:
--   Loc Dens Vol S
-- statement:
--   Definitions and structural lemmas for Loc Dens Vol S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensVolS.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAChar
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
noncomputable section
namespace PI.VolStabW
namespace VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
variable {F : Type} [Field F] [NumberField F]
theorem af_add (y z : Af F) (w : HeightOneSpectrum (𝓞 F)) : (y + z) w = y w + z w := rfl
theorem af_neg (y : Af F) (w : HeightOneSpectrum (𝓞 F)) : (-y) w = -y w := rfl
theorem af_zero (w : HeightOneSpectrum (𝓞 F)) : (0 : Af F) w = 0 := rfl
theorem adele_pairing_zero_add (y z : Af F) : pairA F 0 (y + z) = pairA F 0 y + pairA F 0 z := by
  show ((0 : Ainf F), y + z) = ((0 : Ainf F), y) + ((0 : Ainf F), z)
  rw [Prod.mk_add_mk, add_zero]
def U0 (I : Finset (HeightOneSpectrum (𝓞 F))) (n : HeightOneSpectrum (𝓞 F) → ℕ) :
    AddSubgroup (Af F) where
  carrier := {y | (∀ w, y w ∈ w.adicCompletionIntegers F) ∧
    ∀ w ∈ I, (unifV w ^ n w)⁻¹ * y w ∈ w.adicCompletionIntegers F}
  zero_mem' := ⟨fun w => by rw [af_zero]; exact zero_mem _, fun w _ => by rw [af_zero, mul_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · rw [af_add]; exact add_mem (hy1 w) (hz1 w)
    · rw [af_add, mul_add]; exact add_mem (hy2 w hw) (hz2 w hw)
  neg_mem' := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · rw [af_neg]; exact neg_mem (hy1 w)
    · rw [af_neg, mul_neg]; exact neg_mem (hy2 w hw)
def lamPsi (ψ : AddChar (AF F) ℂ) : Submodule (𝓞 F) F where
  carrier := {a | ∀ r : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((r : F) * a))) = 1}
  add_mem' := by
    intro a b ha hb r
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_add, map_add, adele_pairing_zero_add, AddChar.map_add_eq_mul, ha r, hb r, one_mul]
  zero_mem' := by
    intro r
    rw [mul_zero, map_zero]
    exact AddChar.map_zero_eq_one ψ
  smul_mem' := by
    intro c a ha r
    simp only [Set.mem_setOf_eq] at ha ⊢
    have := ha (r * c)
    rw [Algebra.smul_def]
    convert this using 4
    push_cast
    rw [mul_assoc]
def chiInf (ψ : AddChar (AF F) ℂ) : AddChar (InfiniteAdeleRing F) ℂ where
  toFun x := ψ (pairA F x 0)
  map_zero_eq_one' := by
    show ψ (pairA F 0 0) = 1
    exact AddChar.map_zero_eq_one ψ
  map_add_eq_mul' x y := by
    show ψ (pairA F (x + y) 0) = ψ (pairA F x 0) * ψ (pairA F y 0)
    rw [← AddChar.map_add_eq_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · show x + y = x + y
      rfl
    · show (0 : Af F) = 0 + 0
      rw [add_zero]
end VolAAW
end PI.VolStabW


