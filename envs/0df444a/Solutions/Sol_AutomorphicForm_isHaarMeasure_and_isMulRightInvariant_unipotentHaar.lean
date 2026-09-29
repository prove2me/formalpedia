-- Prove2me | solution 1 for AutomorphicForm.isHaarMeasure_and_isMulRightInvariant_unipotentHaar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/50fb3a24-6189-5406-aed8-c6973c70b437

import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm
open scoped ENNReal

noncomputable section

namespace UnipotentHaarProperties

variable (K : Type*) [Field K] [NumberField K]

private theorem coe_toAdelicUnipotent (x : AdeleRing (𝓞 K) K) :
    ((toAdelicUnipotent K x : adelicUnipotent K) : AdelicGL2 (𝓞 K) K) = unipotentGL2 x := rfl

private theorem toAdelicUnipotent_add (x y : AdeleRing (𝓞 K) K) :
    toAdelicUnipotent K (x + y) = toAdelicUnipotent K x * toAdelicUnipotent K y := by
  apply Subtype.ext
  change unipotentGL2 (x + y) = unipotentGL2 x * unipotentGL2 y
  exact unipotentGL2_add x y

private def entry01 (g : AdelicGL2 (𝓞 K) K) : AdeleRing (𝓞 K) K :=
  (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1

@[scoped simp] private theorem entry01_unipotentGL2 (x : AdeleRing (𝓞 K) K) :
    entry01 K (unipotentGL2 x) = x := by
  simp [entry01, unipotentGL2_coe]

private def ofN (n : adelicUnipotent K) : AdeleRing (𝓞 K) K := entry01 K (n : AdelicGL2 (𝓞 K) K)

private theorem ofN_toAdelicUnipotent (x : AdeleRing (𝓞 K) K) : ofN K (toAdelicUnipotent K x) = x := by
  simp [ofN, coe_toAdelicUnipotent]

private theorem exists_eq_toAdelicUnipotent (n : adelicUnipotent K) :
    ∃ x : AdeleRing (𝓞 K) K, toAdelicUnipotent K x = n := by
  obtain ⟨n, y, hy⟩ := n
  refine ⟨y.toAdd, Subtype.ext ?_⟩
  change unipotentGL2 y.toAdd = n
  rw [← hy]
  rfl

private theorem toAdelicUnipotent_ofN (n : adelicUnipotent K) : toAdelicUnipotent K (ofN K n) = n := by
  obtain ⟨x, rfl⟩ := exists_eq_toAdelicUnipotent K n
  rw [ofN_toAdelicUnipotent]

private theorem toAdelicUnipotent_surjective : Function.Surjective (toAdelicUnipotent K) :=
  fun n => ⟨ofN K n, toAdelicUnipotent_ofN K n⟩

private theorem continuous_unipotentGL2 :
    Continuous fun x : AdeleRing (𝓞 K) K => (unipotentGL2 x : AdelicGL2 (𝓞 K) K) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : AdeleRing (𝓞 K) K =>
      ((unipotentGL2 x : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    simp only [unipotentGL2_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun x : AdeleRing (𝓞 K) K =>
        (((unipotentGL2 x : AdelicGL2 (𝓞 K) K)⁻¹ : AdelicGL2 (𝓞 K) K) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) =
        fun x => !![1, -x; 0, 1] := by
      funext x
      rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_toAdelicUnipotent : Continuous (toAdelicUnipotent K) :=
  (continuous_unipotentGL2 K).subtype_mk _

private theorem continuous_entry01 : Continuous (entry01 K) :=
  (Units.continuous_val).matrix_elem 0 1

private theorem continuous_ofN : Continuous (ofN K) :=
  (continuous_entry01 K).comp continuous_subtype_val

private theorem measurable_toAdelicUnipotent : Measurable (toAdelicUnipotent K) :=
  (continuous_toAdelicUnipotent K).measurable

private theorem measurable_ofN : Measurable (ofN K) :=
  (continuous_ofN K).measurable

private def eN : AdeleRing (𝓞 K) K ≃ᵐ adelicUnipotent K where
  toFun := toAdelicUnipotent K
  invFun := ofN K
  left_inv := ofN_toAdelicUnipotent K
  right_inv := toAdelicUnipotent_ofN K
  measurable_toFun := measurable_toAdelicUnipotent K
  measurable_invFun := measurable_ofN K

private theorem coe_eN : ⇑(eN K) = toAdelicUnipotent K := rfl

private theorem preimage_toAdelicUnipotent_eq_image (s : Set (adelicUnipotent K)) :
    toAdelicUnipotent K ⁻¹' s = ofN K '' s :=
  congrFun (Set.image_eq_preimage_of_inverse (toAdelicUnipotent_ofN K) (ofN_toAdelicUnipotent K)).symm s

private theorem adelicBox_ne : (adelicAddHaar (𝓞 K) K) (adelicBox K) ≠ 0 ∧
    (adelicAddHaar (𝓞 K) K) (adelicBox K) ≠ ⊤ :=
  ⟨(adelicAddHaar_adelicBox_pos K).ne', (adelicAddHaar_adelicBox_lt_top K).ne⟩

private theorem unipotentHaar_eq : unipotentHaar K =
    Measure.map (eN K) (((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K) :=
  rfl

private theorem unipotentHaar_apply (s : Set (adelicUnipotent K)) (hs : MeasurableSet s) :
    unipotentHaar K s =
      ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ * adelicAddHaar (𝓞 K) K (ofN K '' s) := by
  rw [unipotentHaar_eq, Measure.map_apply (eN K).measurable hs, Measure.smul_apply, smul_eq_mul,
    coe_eN, preimage_toAdelicUnipotent_eq_image]

private theorem map_mul_toAdelicUnipotent (a : AdeleRing (𝓞 K) K) :
    Measure.map (fun n => toAdelicUnipotent K a * n) (unipotentHaar K) = unipotentHaar K ∧
    Measure.map (fun n => n * toAdelicUnipotent K a) (unipotentHaar K) = unipotentHaar K := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  set c : ℝ≥0∞ := ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹
  have hmeas : Measurable (toAdelicUnipotent K) := measurable_toAdelicUnipotent K
  have hL : (fun n => toAdelicUnipotent K a * n) ∘ toAdelicUnipotent K =
      toAdelicUnipotent K ∘ fun x => a + x := by
    funext x
    simp [toAdelicUnipotent_add]
  have hR : (fun n => n * toAdelicUnipotent K a) ∘ toAdelicUnipotent K =
      toAdelicUnipotent K ∘ fun x => a + x := by
    funext x
    simp [Function.comp, ← toAdelicUnipotent_add, add_comm]
  have hinv : Measure.map (fun x => a + x) (c • adelicAddHaar (𝓞 K) K) =
      c • adelicAddHaar (𝓞 K) K := by
    rw [Measure.map_smul, map_add_left_eq_self]
  constructor
  · rw [unipotentHaar_eq, coe_eN, Measure.map_map (measurable_const_mul _) hmeas, hL,
      ← Measure.map_map hmeas (measurable_const_add a), hinv]
  · rw [unipotentHaar_eq, coe_eN, Measure.map_map (measurable_mul_const _) hmeas, hR,
      ← Measure.map_map hmeas (measurable_const_add a), hinv]

private theorem isHaarMeasure_unipotentHaar : (unipotentHaar K).IsHaarMeasure where
  lt_top_of_isCompact := by
    intro C hC
    haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
    rw [unipotentHaar_apply K C hC.measurableSet]
    refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 (adelicBox_ne K).1)) ?_
    exact (hC.image (continuous_ofN K)).measure_lt_top
  map_mul_left_eq_self := by
    intro n
    obtain ⟨a, rfl⟩ := exists_eq_toAdelicUnipotent K n
    exact (map_mul_toAdelicUnipotent K a).1
  open_pos := by
    intro U hU hne
    haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
    rw [unipotentHaar_apply K U hU.measurableSet, ← preimage_toAdelicUnipotent_eq_image]
    refine mul_ne_zero (ENNReal.inv_ne_zero.2 (adelicBox_ne K).2) ?_
    exact ((hU.preimage (continuous_toAdelicUnipotent K)).measure_pos _
      (hne.preimage (toAdelicUnipotent_surjective K))).ne'

private theorem isMulRightInvariant_unipotentHaar : (unipotentHaar K).IsMulRightInvariant := by
  refine ⟨fun n => ?_⟩
  obtain ⟨a, rfl⟩ := exists_eq_toAdelicUnipotent K n
  exact (map_mul_toAdelicUnipotent K a).2

end UnipotentHaarProperties
p2m_reactivate "P2MW.S_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar.UnipotentHaarProperties"

theorem solution (K : Type*) [Field K]
    [NumberField K] :
    (AutomorphicForm.unipotentHaar K).IsHaarMeasure ∧
      (AutomorphicForm.unipotentHaar K).IsMulRightInvariant :=
  ⟨UnipotentHaarProperties.isHaarMeasure_unipotentHaar K,
    UnipotentHaarProperties.isMulRightInvariant_unipotentHaar K⟩

end
p2m_reactivate "P2MW.S_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar.UnipotentHaarProperties"

end S_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar
end P2MW
export P2MW.S_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar (solution)
