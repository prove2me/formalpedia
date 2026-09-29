-- Prove2me | solution 1 for AutomorphicForm.lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9b2f4c8a-c57b-52f4-a2cb-f85fd77e485c

import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj.AutomorphicForm IsDedekindDomain"

open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalCentreUnipotent rationalCentreUnipotentHaar adelicUnipotent toAdelicUnipotent unipotentHaar unipotentGL2 unipotentGL2_coe AdelicGL2 globalPoints centralScalar uniformizerIdele"
p2m_open "AutomorphicForm"

variable (K : Type) [Field K] [NumberField K]

theorem centralScalar_mul_comm' (u : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K u * g = g * centralScalar (𝓞 K) K u := by
  refine Units.ext ?_
  change Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K)
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

theorem diagOne_mul_unipotentGL2_mul_inv' (τ : (AdeleRing (𝓞 K) K)ˣ) (x : AdeleRing (𝓞 K) K) :
    diagOne τ * unipotentGL2 x * (diagOne τ)⁻¹ = unipotentGL2 ((τ : AdeleRing (𝓞 K) K) * x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [← map_inv]
  change (Matrix.diagonal ![((τ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1] * !![1, x; 0, 1] *
      Matrix.diagonal ![((τ⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1]) i j = !![1, (τ : AdeleRing (𝓞 K) K) * x; 0, 1] i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_mul, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp

abbrev ratCentral (a : Kˣ) : AdelicGL2 (𝓞 K) K :=
  globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)

theorem ratCentral_eq_centralScalar (a : Kˣ) :
    ratCentral K a = centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (a : K)) i j) =
    (Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem conj_ratCentral_mul_unipotentGL2 (τ u : (AdeleRing (𝓞 K) K)ˣ) (a : Kˣ) (y : AdeleRing (𝓞 K) K) :
    (diagOne τ * centralScalar (𝓞 K) K u) * (ratCentral K a * unipotentGL2 y) * (diagOne τ * centralScalar (𝓞 K) K u)⁻¹ =
      ratCentral K a * unipotentGL2 ((τ : AdeleRing (𝓞 K) K) * y) := by
  have hz : ∀ g : AdelicGL2 (𝓞 K) K, ratCentral K a * g = g * ratCentral K a := fun g => by
    rw [ratCentral_eq_centralScalar, centralScalar_mul_comm']
  set c := diagOne τ * centralScalar (𝓞 K) K u with hc
  rw [← mul_assoc c, ← hz c, mul_assoc (ratCentral K a), mul_assoc (ratCentral K a)]
  congr 1
  rw [hc, mul_inv_rev,
    show diagOne τ * centralScalar (𝓞 K) K u * unipotentGL2 y * ((centralScalar (𝓞 K) K u)⁻¹ * (diagOne τ)⁻¹) =
      diagOne τ * (centralScalar (𝓞 K) K u * unipotentGL2 y * (centralScalar (𝓞 K) K u)⁻¹) * (diagOne τ)⁻¹ by group,
    centralScalar_mul_comm' K u, mul_inv_cancel_right, diagOne_mul_unipotentGL2_mul_inv']

theorem continuous_unipotentGL2 : Continuous (fun y : AdeleRing (𝓞 K) K => (unipotentGL2 y : AdelicGL2 (𝓞 K) K)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Function.comp_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : ∀ y : AdeleRing (𝓞 K) K, (↑((unipotentGL2 y : AdelicGL2 (𝓞 K) K)⁻¹) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
        !![1, -y; 0, 1] := fun y => rfl
    simp_rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem ratCentral_mul_unipotentGL2_mem (a : Kˣ) (y : AdeleRing (𝓞 K) K) :
    ratCentral K a * unipotentGL2 y ∈ rationalCentreUnipotent K :=
  Subgroup.mul_mem_sup ⟨a, rfl⟩ ⟨Multiplicative.ofAdd y, rfl⟩

theorem lintegral_rationalCentreUnipotentHaar (G : rationalCentreUnipotent K → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂(rationalCentreUnipotentHaar K) =
      ∑' a : Kˣ, ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ *
        ∫⁻ y, G ⟨ratCentral K a * unipotentGL2 y, ratCentral_mul_unipotentGL2_mem K a y⟩ ∂(adelicAddHaar (𝓞 K) K) := by
  rw [rationalCentreUnipotentHaar, lintegral_sum_measure]
  refine tsum_congr fun a => ?_

  have hι : Measurable (fun n : adelicUnipotent K =>
      (⟨ratCentral K a * (n : AdelicGL2 (𝓞 K) K), Subgroup.mul_mem_sup ⟨a, rfl⟩ n.2⟩ : rationalCentreUnipotent K)) :=
    ((continuous_const.mul continuous_subtype_val).measurable).subtype_mk
  rw [lintegral_map hG hι, unipotentHaar]
  have hto : Measurable (toAdelicUnipotent K) := by
    refine (Continuous.subtype_mk ?_ _).measurable
    exact (continuous_unipotentGL2 K)
  have hGι : Measurable (fun n : adelicUnipotent K =>
      G ⟨ratCentral K a * (n : AdelicGL2 (𝓞 K) K), Subgroup.mul_mem_sup ⟨a, rfl⟩ n.2⟩) := hG.comp hι
  rw [lintegral_map hGι hto, lintegral_smul_measure, smul_eq_mul]
  rfl

open scoped Pointwise in
theorem lintegral_comp_mul_adelicAddHaar (τ : (AdeleRing (𝓞 K) K)ˣ) (φ : AdeleRing (𝓞 K) K → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ y, φ ((τ : AdeleRing (𝓞 K) K) * y) ∂(adelicAddHaar (𝓞 K) K) =
      (((distribHaarChar (AdeleRing (𝓞 K) K) τ)⁻¹ : ℝ≥0) : ℝ≥0∞) * ∫⁻ y, φ y ∂(adelicAddHaar (𝓞 K) K) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  haveI : (adelicAddHaar (𝓞 K) K).Regular := by
    unfold adelicAddHaar Measure.addHaar; infer_instance
  have hmap : (adelicAddHaar (𝓞 K) K).map (fun y => (τ : AdeleRing (𝓞 K) K) * y) =
      (((distribHaarChar (AdeleRing (𝓞 K) K) τ)⁻¹ : ℝ≥0) : ℝ≥0∞) • adelicAddHaar (𝓞 K) K := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul,
      show (fun y => (τ : AdeleRing (𝓞 K) K) * y) ⁻¹' s = τ⁻¹ • s from Set.preimage_smul τ s,
      ← distribHaarChar_mul (adelicAddHaar (𝓞 K) K) τ⁻¹ s, map_inv]
  rw [← lintegral_map hφ (measurable_const_mul _), hmap, lintegral_smul_measure, smul_eq_mul]

theorem heckeGen_eq_diagOne_uniformizerIdele (v : HeightOneSpectrum (𝓞 K)) :
    heckeGen (𝓞 K) K v = diagOne (uniformizerIdele K v) := rfl

theorem coe_inv_distribHaarChar_uniformizerIdele (v : HeightOneSpectrum (𝓞 K)) :
    (((distribHaarChar (AdeleRing (𝓞 K) K) (uniformizerIdele K v))⁻¹ : ℝ≥0) : ℝ≥0∞) =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) := by
  have h := NumberField.TateGlobal.ideleNorm_uniformizerIdele K v
  rw [NumberField.TateGlobal.ideleNorm] at h
  have h' : distribHaarChar (AdeleRing (𝓞 K) K) (uniformizerIdele K v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ := by
    apply NNReal.coe_injective
    rw [h, NNReal.coe_inv, NNReal.coe_natCast]
  rw [h', inv_inv, ENNReal.coe_natCast]

theorem lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj
    (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hb : ∀ y : AdelicGL2 (𝓞 K) K, y ∈ rationalCentreUnipotent K ↔
      (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * y * (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹ ∈
        rationalCentreUnipotent K)
    (F : rationalCentreUnipotent K → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F ⟨(heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * (x : AdelicGL2 (𝓞 K) K) *
        (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹, (hb (x : AdelicGL2 (𝓞 K) K)).mp x.2⟩
      ∂(rationalCentreUnipotentHaar K) =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) * ∫⁻ x, F x ∂(rationalCentreUnipotentHaar K) := by
  set τ := uniformizerIdele K v with hτ
  set b := heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u with hb_def
  have hbτ : b = diagOne τ * centralScalar (𝓞 K) K u := rfl

  set G : rationalCentreUnipotent K → ℝ≥0∞ := fun x => F ⟨b * (x : AdelicGL2 (𝓞 K) K) * b⁻¹, (hb _).mp x.2⟩ with hG_def
  have hG : Measurable G :=
    hF.comp (((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable.subtype_mk)
  change ∫⁻ x, G x ∂(rationalCentreUnipotentHaar K) = _
  rw [lintegral_rationalCentreUnipotentHaar K G hG, lintegral_rationalCentreUnipotentHaar K F hF, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun a => ?_

  set Φ : AdeleRing (𝓞 K) K → ℝ≥0∞ := fun y => F ⟨ratCentral K a * unipotentGL2 y, ratCentral_mul_unipotentGL2_mem K a y⟩ with hΦ_def
  have hΦ : Measurable Φ := hF.comp ((continuous_const.mul (continuous_unipotentGL2 K)).measurable.subtype_mk)
  have hGΦ : ∀ y : AdeleRing (𝓞 K) K,
      G ⟨ratCentral K a * unipotentGL2 y, ratCentral_mul_unipotentGL2_mem K a y⟩ = Φ ((τ : AdeleRing (𝓞 K) K) * y) := by
    intro y
    simp only [hG_def, hΦ_def]
    refine congrArg F (Subtype.ext ?_)
    change b * (ratCentral K a * unipotentGL2 y) * b⁻¹ = ratCentral K a * unipotentGL2 ((τ : AdeleRing (𝓞 K) K) * y)
    rw [hbτ]
    exact conj_ratCentral_mul_unipotentGL2 K τ u a y
  simp_rw [hGΦ]
  rw [lintegral_comp_mul_adelicAddHaar K τ Φ hΦ, coe_inv_distribHaarChar_uniformizerIdele]
  ring

end AutomorphicForm

end

theorem solution
    (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hb : ∀ y : AdelicGL2 (𝓞 K) K, y ∈ rationalCentreUnipotent K ↔
      (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * y * (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹ ∈
        rationalCentreUnipotent K)
    (F : rationalCentreUnipotent K → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F ⟨(heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * (x : AdelicGL2 (𝓞 K) K) *
        (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹, (hb (x : AdelicGL2 (𝓞 K) K)).mp x.2⟩
      ∂(rationalCentreUnipotentHaar K) =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) * ∫⁻ x, F x ∂(rationalCentreUnipotentHaar K) :=
  AutomorphicForm.lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj K v u hb F hF

end S_AutomorphicForm_lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj
end P2MW
export P2MW.S_AutomorphicForm_lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj (solution)
