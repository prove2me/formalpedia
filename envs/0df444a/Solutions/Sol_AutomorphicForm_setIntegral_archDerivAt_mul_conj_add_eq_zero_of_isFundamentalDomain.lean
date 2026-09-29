-- Prove2me | solution 1 for AutomorphicForm.setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2d172de3-0158-526d-8945-7ac9f091ce51

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Calculus.ParametricIntegral
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace UnitSymFlow25

section DetOne

private def dA : GL (Fin 2) ℝ where
  val := !![1, 0; 0, 2]
  inv := !![1, 0; 0, 2⁻¹]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def dB : GL (Fin 2) ℝ where
  val := !![2, 0; 0, 1]
  inv := !![2⁻¹, 0; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def sw : GL (Fin 2) ℝ where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def dE (t : ℝ) : GL (Fin 2) ℝ where
  val := !![Real.exp (-t), 0; 0, 1]
  inv := !![Real.exp t, 0; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]

private theorem rel_E (t : ℝ) : unipotentGL2 t * unipotentGL2 t * dB = dB * unipotentGL2 t := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dB, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem rel_Fm (t : ℝ) : lowerUnipotentGL2 t * lowerUnipotentGL2 t * dA = dA * lowerUnipotentGL2 t := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dA, lowerUnipotentGL2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem rel_H (t : ℝ) : splitTorusGL2 t * dE t * sw = sw * dE t := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dE, sw, splitTorusGL2, Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]

private theorem map_eq_one_of_rel {G C : Type*} [Group G] [CommGroup C] (ψ : G →* C) {m u a : G}
    (h : m * u * a = a * u) : ψ m = 1 := by
  have h' := congrArg ψ h
  rw [map_mul, map_mul, map_mul, mul_comm (ψ a) (ψ u), mul_assoc] at h'
  exact mul_eq_right.mp h'

variable {K : Type} [Field K] [NumberField K]

theorem det_archFlowAt {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    Matrix.GeneralLinearGroup.det (archFlowAt hw d t) = 1 := by
  let ψ : GL (Fin 2) ℝ →* (AdeleRing (𝓞 K) K)ˣ := (Matrix.GeneralLinearGroup.det).comp (archRealGLAt hw)
  show ψ (archFlowMatrix d t) = 1
  cases d
  · exact map_eq_one_of_rel ψ (rel_H t)
  · exact map_eq_one_of_rel ψ (rel_E t)
  · exact map_eq_one_of_rel ψ (rel_Fm t)

theorem archFlowAt_inv {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    (archFlowAt hw d t)⁻¹ = archFlowAt hw d (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← archFlowAt_add, add_neg_cancel, archFlowAt_zero])

end DetOne

section Slab

open scoped Pointwise

variable {K : Type} [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

abbrev dn (g : AdelicGL2 (𝓞 K) K) : ℝ := ideleNorm K (Matrix.GeneralLinearGroup.det g)

abbrev slab (K : Type) [Field K] [NumberField K] (a b : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

abbrev Γp (K : Type) [Field K] [NumberField K] : Subgroup (AdelicGL2 (𝓞 K) K) :=
  (globalPoints (𝓞 K) K).range

private scoped instance instCountableK : Countable K :=
  (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable

private scoped instance instCountableΓ : Countable ↥(Γp K) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (GL (Fin 2) K) := Units.val_injective.countable
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 K) K)).countable

theorem dn_mul (g h : AdelicGL2 (𝓞 K) K) : dn (g * h) = dn g * dn h := by
  show ideleNorm K _ = _
  rw [map_mul, ideleNorm_mul]

theorem dn_globalPoints_mul (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    dn (globalPoints (𝓞 K) K γ * g) = dn g := by
  rw [dn_mul]
  show ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ)) * dn g = dn g
  rw [AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem dn_subtype_mul (γ : ↥(Γp K)) (g : AdelicGL2 (𝓞 K) K) : dn ((γ : AdelicGL2 (𝓞 K) K) * g) = dn g := by
  obtain ⟨_, γ', rfl⟩ := γ
  exact dn_globalPoints_mul γ' g

theorem dn_mul_archFlowAt {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ)
    (g : AdelicGL2 (𝓞 K) K) : dn (g * archFlowAt hw d t) = dn g := by
  rw [dn_mul]
  show dn g * ideleNorm K (Matrix.GeneralLinearGroup.det (archFlowAt hw d t)) = dn g
  rw [det_archFlowAt]
  simp [ideleNorm]

theorem measurableSet_slab (a b : ℝ) : MeasurableSet (slab K a b) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K a b

theorem preimage_subtype_mul_slab (γ : ↥(Γp K)) (a b : ℝ) :
    (fun g : AdelicGL2 (𝓞 K) K => (γ : AdelicGL2 (𝓞 K) K) * g) ⁻¹' slab K a b = slab K a b := by
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [show ideleNorm K (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 K) K) * g)) = dn g from
    dn_subtype_mul γ g]

theorem preimage_mul_archFlowAt_slab {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) (a b : ℝ) :
    (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAt hw d t) ⁻¹' slab K a b = slab K a b := by
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [show ideleNorm K (Matrix.GeneralLinearGroup.det (g * archFlowAt hw d t)) = dn g from
    dn_mul_archFlowAt hw d t g]

theorem mul_archFlowAt_mem_slab {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) {a b : ℝ}
    {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ slab K a b) : g * archFlowAt hw d t ∈ slab K a b := by
  show dn (g * archFlowAt hw d t) ∈ Set.Icc a b
  rw [dn_mul_archFlowAt]
  exact hg

theorem image_mul_archFlowAt_subset {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) {a b : ℝ}
    {𝓕 : Set (AdelicGL2 (𝓞 K) K)} (h : 𝓕 ⊆ slab K a b) :
    (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAt hw d t) '' 𝓕 ⊆ slab K a b := by
  rintro _ ⟨g, hg, rfl⟩
  exact mul_archFlowAt_mem_slab hw d t (h hg)

theorem smulInvariantMeasure_restrict (Γ : Subgroup (AdelicGL2 (𝓞 K) K))
    (μ : Measure (AdelicGL2 (𝓞 K) K)) [SMulInvariantMeasure ↥Γ (AdelicGL2 (𝓞 K) K) μ]
    {T : Set (AdelicGL2 (𝓞 K) K)} (hT : MeasurableSet T)
    (hΓT : ∀ γ : ↥Γ, (fun g : AdelicGL2 (𝓞 K) K => γ • g) ⁻¹' T = T) :
    SMulInvariantMeasure ↥Γ (AdelicGL2 (𝓞 K) K) (μ.restrict T) := by
  refine ⟨fun γ A hA => ?_⟩
  rw [Measure.restrict_apply (hA.preimage (measurable_const_smul _)), Measure.restrict_apply hA]
  conv_lhs => rw [← hΓT γ, ← Set.preimage_inter]
  exact SMulInvariantMeasure.measure_preimage_smul γ (hA.inter hT)

theorem smulInvariantMeasure_slab (a b : ℝ) :
    SMulInvariantMeasure ↥(Γp K) (AdelicGL2 (𝓞 K) K) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) :=
  smulInvariantMeasure_restrict (Γp K) (adelicGLHaar (Fin 2) (𝓞 K) K) (measurableSet_slab a b)
    (fun γ => preimage_subtype_mul_slab γ a b)

theorem measurePreserving_mul_right' (k : AdelicGL2 (𝓞 K) K) :
    MeasurePreserving (fun g : AdelicGL2 (𝓞 K) K => g * k)
      (adelicGLHaar (Fin 2) (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  exact measurePreserving_mul_right (adelicGLHaar (Fin 2) (𝓞 K) K) k

theorem isFundamentalDomain_image_mul_archFlowAt {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ)
    (a b : ℝ) {𝓕 : Set (AdelicGL2 (𝓞 K) K)}
    (h𝓕 : IsFundamentalDomain ↥(Γp K) 𝓕 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b))) :
    IsFundamentalDomain ↥(Γp K) ((fun g : AdelicGL2 (𝓞 K) K => g * archFlowAt hw d t) '' 𝓕)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
  have hcoe : (⇑(Equiv.mulRight (archFlowAt hw d t)) : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K) =
      fun g => g * archFlowAt hw d t := Equiv.coe_mulRight _
  have hqmp : Measure.QuasiMeasurePreserving (⇑(Equiv.mulRight (archFlowAt hw d t)).symm)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b))
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
    rw [Equiv.mulRight_symm, Equiv.coe_mulRight, archFlowAt_inv]
    have h1 := (measurePreserving_mul_right' (K := K) (archFlowAt hw d (-t))).restrict_preimage
      (measurableSet_slab (K := K) a b)
    rw [preimage_mul_archFlowAt_slab] at h1
    exact h1.quasiMeasurePreserving
  have h := h𝓕.image_of_equiv (Equiv.mulRight (archFlowAt hw d t)) hqmp (Equiv.refl _) (fun γ g => by
    show (((Equiv.refl _ γ : ↥(Γp K)) : AdelicGL2 (𝓞 K) K) * g) * archFlowAt hw d t =
      (γ : AdelicGL2 (𝓞 K) K) * (g * archFlowAt hw d t)
    rw [Equiv.refl_apply, mul_assoc])
  rwa [hcoe] at h

theorem setIntegral_comp_mul_archFlowAt_eq {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ)
    (a b : ℝ) {𝓕 : Set (AdelicGL2 (𝓞 K) K)} (h𝓕s : 𝓕 ⊆ slab K a b)
    (h𝓕 : IsFundamentalDomain ↥(Γp K) 𝓕 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)))
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * g) = f g) :
    ∫ g in 𝓕, f (g * archFlowAt hw d t) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ g in 𝓕, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := smulInvariantMeasure_slab (K := K) a b
  have hemb : MeasurableEmbedding (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAt hw d t) :=
    (Homeomorph.mulRight (archFlowAt hw d t)).measurableEmbedding
  have hsub := image_mul_archFlowAt_subset hw d t h𝓕s
  have hinv : ∀ (γ : ↥(Γp K)) (g : AdelicGL2 (𝓞 K) K), f (γ • g) = f g := by
    rintro ⟨_, γ', rfl⟩ g
    exact hf γ' g
  calc ∫ g in 𝓕, f (g * archFlowAt hw d t) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ h in (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAt hw d t) '' 𝓕, f h ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        ((measurePreserving_mul_right' (K := K) (archFlowAt hw d t)).setIntegral_image_emb hemb f 𝓕).symm
    _ = ∫ h in (fun g : AdelicGL2 (𝓞 K) K => g * archFlowAt hw d t) '' 𝓕, f h
          ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
        rw [Measure.restrict_restrict_of_subset hsub]
    _ = ∫ h in 𝓕, f h ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) :=
        (isFundamentalDomain_image_mul_archFlowAt hw d t a b h𝓕).setIntegral_eq h𝓕 hinv
    _ = ∫ g in 𝓕, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        rw [Measure.restrict_restrict_of_subset h𝓕s]

end Slab

section Deriv

variable {K : Type} [Field K] [NumberField K]

theorem hasDerivAt_comp_mul_archFlowAt {w : InfinitePlace K} {hw : w.IsReal} (d : ArchDir)
    {x : AdelicGL2 (𝓞 K) K → ℂ} (hxs : IsArchSmoothAt hw x) (g : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x (g * archFlowAt hw d s)) (archDerivAt hw d x (g * archFlowAt hw d t)) t := by
  have h0 : HasDerivAt (fun s : ℝ => x (g * archFlowAt hw d t * archFlowAt hw d s))
      (archDerivAt hw d x (g * archFlowAt hw d t)) 0 :=
    (hxs.differentiableAt_flow d (g * archFlowAt hw d t)).hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => x (g * archFlowAt hw d (t + s)))
      (archDerivAt hw d x (g * archFlowAt hw d t)) 0 := by
    have hfun : (fun s : ℝ => x (g * archFlowAt hw d t * archFlowAt hw d s)) =
        fun s : ℝ => x (g * archFlowAt hw d (t + s)) := by
      funext s; rw [archFlowAt_add, mul_assoc]
    rwa [hfun] at h0
  have h1' : HasDerivAt (fun s : ℝ => x (g * archFlowAt hw d (t + s)))
      (archDerivAt hw d x (g * archFlowAt hw d t)) (-t + t) := by rwa [neg_add_cancel]
  have h2 := h1'.comp_const_add (-t) t
  simp only [add_neg_cancel_left] at h2
  exact h2

private theorem norm_mul_conj_le {a b : ℂ} {B : ℝ} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) : ‖a * conj b‖ ≤ B * B := by
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg a).trans ha)

private theorem norm_add_le' {a b c d : ℂ} {B : ℝ} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B)
    (hd : ‖d‖ ≤ B) : ‖a * conj b + c * conj d‖ ≤ B * B + B * B :=
  (norm_add_le _ _).trans (add_le_add (norm_mul_conj_le ha hb) (norm_mul_conj_le hc hd))

end Deriv

section Main

attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

theorem main
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (X : ArchDir)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ slab K e₁ e₂)
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K e₁ e₂)))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAt hw x) (hx's : IsArchSmoothAt hw x')
    (hDx : Continuous (archDerivAt hw X x)) (hDx' : Continuous (archDerivAt hw X x'))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧ ‖archDerivAt hw X x g‖ ≤ B ∧ ‖archDerivAt hw X x' g‖ ≤ B) :
    ∫ g in 𝓕, (archDerivAt hw X x g * conj (x' g) + x g * conj (archDerivAt hw X x' g))
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ

  let Φ : ℝ → AdelicGL2 (𝓞 K) K → ℂ := fun t g =>
    x (g * archFlowAt hw X t) * conj (x' (g * archFlowAt hw X t))
  let Φ' : ℝ → AdelicGL2 (𝓞 K) K → ℂ := fun t g =>
    archDerivAt hw X x (g * archFlowAt hw X t) * conj (x' (g * archFlowAt hw X t)) +
      x (g * archFlowAt hw X t) * conj (archDerivAt hw X x' (g * archFlowAt hw X t))

  have hfin : μ 𝓕 < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K e₁ e₂ he₁ he 𝓕 h𝓕
    rwa [Set.inter_eq_left.mpr h𝓕s] at h
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.mpr hfin.ne

  have hΦc : ∀ t, Continuous (Φ t) := fun t =>
    (hxc.comp (continuous_mul_const (archFlowAt hw X t))).mul
      (Complex.continuous_conj.comp (hx'c.comp (continuous_mul_const (archFlowAt hw X t))))
  have hΦ'c : ∀ t, Continuous (Φ' t) := fun t =>
    ((hDx.comp (continuous_mul_const (archFlowAt hw X t))).mul
      (Complex.continuous_conj.comp (hx'c.comp (continuous_mul_const (archFlowAt hw X t))))).add
    ((hxc.comp (continuous_mul_const (archFlowAt hw X t))).mul
      (Complex.continuous_conj.comp (hDx'.comp (continuous_mul_const (archFlowAt hw X t)))))

  have hΦb : ∀ t, ∀ g ∈ 𝓕, ‖Φ t g‖ ≤ B * B := fun t g hg => by
    obtain ⟨h1, h2, -, -⟩ := hB _ (mul_archFlowAt_mem_slab hw X t (h𝓕s hg))
    exact norm_mul_conj_le h1 h2
  have hΦ'b : ∀ t, ∀ g ∈ 𝓕, ‖Φ' t g‖ ≤ B * B + B * B := fun t g hg => by
    obtain ⟨h1, h2, h3, h4⟩ := hB _ (mul_archFlowAt_mem_slab hw X t (h𝓕s hg))
    exact norm_add_le' h3 h2 h1 h4

  have hint : Integrable (Φ 0) (μ.restrict 𝓕) :=
    Measure.integrableOn_of_bounded hfin.ne (hΦc 0).aestronglyMeasurable
      ((ae_restrict_iff' h𝓕m).mpr (Filter.Eventually.of_forall fun g hg => hΦb 0 g hg))

  have hdiff : ∀ (g : AdelicGL2 (𝓞 K) K) (t : ℝ), HasDerivAt (fun s => Φ s g) (Φ' t g) t := fun g t => by
    have ha := hasDerivAt_comp_mul_archFlowAt X hxs g t
    have hb := (hasDerivAt_comp_mul_archFlowAt X hx's g t).star
    exact ha.mul hb

  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (F := Φ) (F' := Φ')
    (x₀ := (0 : ℝ)) (s := Set.univ) (bound := fun _ => B * B + B * B) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hΦc t).aestronglyMeasurable) hint
    (hΦ'c 0).aestronglyMeasurable
    ((ae_restrict_iff' h𝓕m).mpr (Filter.Eventually.of_forall fun g hg t _ => hΦ'b t g hg))
    (integrable_const _)
    (Filter.Eventually.of_forall fun g t _ => hdiff g t)
  obtain ⟨-, hderiv⟩ := key

  have hconst : (fun t : ℝ => ∫ g, Φ t g ∂(μ.restrict 𝓕)) = fun _ => ∫ g in 𝓕, x g * conj (x' g) ∂μ := by
    funext t
    exact setIntegral_comp_mul_archFlowAt_eq hw X t e₁ e₂ h𝓕s h𝓕 (fun g => x g * conj (x' g))
      (fun γ g => by show x _ * conj (x' _) = x g * conj (x' g); rw [hx, hx'])
  have hzero : HasDerivAt (fun t : ℝ => ∫ g, Φ t g ∂(μ.restrict 𝓕)) 0 0 := by
    rw [hconst]; exact hasDerivAt_const _ _
  have h0 : ∫ g, Φ' 0 g ∂(μ.restrict 𝓕) = 0 := hderiv.unique hzero
  have hΦ'0 : ∀ g, Φ' 0 g = archDerivAt hw X x g * conj (x' g) + x g * conj (archDerivAt hw X x' g) := by
    intro g
    show archDerivAt hw X x (g * archFlowAt hw X 0) * conj (x' (g * archFlowAt hw X 0)) +
      x (g * archFlowAt hw X 0) * conj (archDerivAt hw X x' (g * archFlowAt hw X 0)) = _
    rw [archFlowAt_zero, mul_one]
  have h1 : ∫ g, Φ' 0 g ∂(μ.restrict 𝓕) =
      ∫ g in 𝓕, (archDerivAt hw X x g * conj (x' g) + x g * conj (archDerivAt hw X x' g)) ∂μ := by
    congr 1
    funext g
    exact hΦ'0 g
  rw [← h1]
  exact h0

end Main

end UnitSymFlow25
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain.UnitSymFlow25"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain.UnitSymFlow25"

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (X : ArchDir)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAt hw x) (hx's : IsArchSmoothAt hw x')
    (hDx : Continuous (archDerivAt hw X x)) (hDx' : Continuous (archDerivAt hw X x'))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧ ‖archDerivAt hw X x g‖ ≤ B ∧ ‖archDerivAt hw X x' g‖ ≤ B) :
    ∫ g in 𝓕, (archDerivAt hw X x g * conj (x' g) + x g * conj (archDerivAt hw X x' g)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 :=
  UnitSymFlow25.main K w hw X e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 x x' hx hx' hxc hx'c hxs hx's hDx hDx' B hB

end S_AutomorphicForm_setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain (solution)
