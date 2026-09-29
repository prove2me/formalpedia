-- Prove2me | solution 1 for AutomorphicForm.setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_of_scalar_mul_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e02baa92-ab8e-5e0d-8f00-41a73b252c78

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_of_scalar_mul_eq_conj
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

namespace PccAlpha

open AutomorphicForm

theorem centralScalar_comm (F : Type) [Field F] [NumberField F]
    (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * g = g * centralScalar (𝓞 F) F z := by
  apply Units.ext
  show (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)) * g.val =
    g.val * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

theorem scalar_comm (F : Type) [Field F] (s : Fˣ) (g : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) s * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
  apply Units.ext
  show (Matrix.scalar (Fin 2) (s : F)) * g.val = g.val * Matrix.scalar (Fin 2) (s : F)
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

theorem globalPoints_scalar (F : Type) [Field F] [NumberField F] (s : Fˣ) :
    globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) s) =
      centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) s) := by
  apply Units.ext
  ext i j
  simp [globalPoints, centralScalar, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

theorem countable_GL2 (F : Type) [Field F] [NumberField F] : Countable (GL (Fin 2) F) := by
  haveI := countable_numberField F
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  exact Function.Injective.countable (f := fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
    (fun a b h => Units.ext h)

theorem restrict_band_preimage_mul (F : Type) [Field F] [NumberField F] (α β : ℝ)
    (k : AdelicGL2 (𝓞 F) F)
    (hk : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det k) = 1)
    (s : Set (AdelicGL2 (𝓞 F) F)) :
    ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
        ((fun x => k * x) ⁻¹' s) =
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) s := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  have hHaar := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hb := NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F α β
  rw [Measure.restrict_apply' hb, Measure.restrict_apply' hb]
  have hset : (fun x => k * x) ⁻¹' s ∩
      {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} =
      (fun x => k * x) ⁻¹'
        (s ∩ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, map_mul,
      NumberField.TateGlobal.ideleNorm_mul, hk, one_mul]
  rw [hset, measure_preimage_mul]

end PccAlpha

open AutomorphicForm in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α)
    (γ₀ : GL (Fin 2) F)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))
    (hΨs : Ψ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (AutomorphicForm.globalPoints (𝓞 F) F)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (z : (AdeleRing (𝓞 F) F)ˣ)
    (s : Fˣ) (h : GL (Fin 2) F)
    (hsh : Matrix.GeneralLinearGroup.scalar (Fin 2) s * γ₀ = h⁻¹ * γ₀ * h) :
    ∫ x in Ψ, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ *
        (AutomorphicForm.centralScalar (𝓞 F) F
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) s * z) * x))
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ x in Ψ, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ *
        (AutomorphicForm.centralScalar (𝓞 F) F z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by

  haveI hBorel := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  have hHaar := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set B : Set (AdelicGL2 (𝓞 F) F) :=
    {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hB
  set Γ : Subgroup (AdelicGL2 (𝓞 F) F) :=
    (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (globalPoints (𝓞 F) F) with hΓ
  set k : AdelicGL2 (𝓞 F) F := globalPoints (𝓞 F) F h with hk
  set S : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) s with hS
  have hkdet : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det k) = 1 :=
    AutomorphicForm.ideleNorm_det_globalPoints h
  have hkdet' : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det k⁻¹) = 1 := by
    show ((distribHaarChar (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det k⁻¹) : NNReal) : ℝ) = 1
    rw [map_inv, map_inv, NNReal.coe_inv, inv_eq_one]
    exact hkdet
  have hSc : ∀ g : GL (Fin 2) F, S * g = g * S := fun g => PccAlpha.scalar_comm F s g

  set F₂ : AdelicGL2 (𝓞 F) F → ℂ := fun y =>
    f (y⁻¹ * globalPoints (𝓞 F) F γ₀ * (centralScalar (𝓞 F) F z * y)) with hF₂
  have hconj : globalPoints (𝓞 F) F γ₀ *
      centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) s) =
      k⁻¹ * globalPoints (𝓞 F) F γ₀ * k := by
    rw [← PccAlpha.globalPoints_scalar, ← map_mul, ← hSc, hsh, map_mul, map_mul, map_inv]
  have hint : ∀ x : AdelicGL2 (𝓞 F) F,
      f (x⁻¹ * globalPoints (𝓞 F) F γ₀ *
        (centralScalar (𝓞 F) F
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) s * z) * x)) =
      F₂ (k * x) := by
    intro x
    simp only [hF₂]
    congr 1
    rw [map_mul, mul_inv_rev]
    have hz := PccAlpha.centralScalar_comm F z
    calc x⁻¹ * globalPoints (𝓞 F) F γ₀ *
          (centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) s) *
            centralScalar (𝓞 F) F z * x)
        = x⁻¹ * (globalPoints (𝓞 F) F γ₀ *
          centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) s)) *
            (centralScalar (𝓞 F) F z * x) := by group
      _ = x⁻¹ * (k⁻¹ * globalPoints (𝓞 F) F γ₀ * k) * (centralScalar (𝓞 F) F z * x) := by rw [hconj]
      _ = x⁻¹ * k⁻¹ * globalPoints (𝓞 F) F γ₀ * ((k * centralScalar (𝓞 F) F z) * x) := by group
      _ = x⁻¹ * k⁻¹ * globalPoints (𝓞 F) F γ₀ * (centralScalar (𝓞 F) F z * k * x) := by rw [hz k]
      _ = _ := by group
  simp_rw [hint]

  have hF₂inv : ∀ (g : Γ) (y : AdelicGL2 (𝓞 F) F), F₂ (g • y) = F₂ y := by
    intro g y
    obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp g.2
    have hc' : γ₀ * c = c * γ₀ := (Subgroup.mem_centralizer_iff.mp hc) γ₀ (Set.mem_singleton γ₀)
    have hcomm : globalPoints (𝓞 F) F γ₀ * (g : AdelicGL2 (𝓞 F) F) =
        (g : AdelicGL2 (𝓞 F) F) * globalPoints (𝓞 F) F γ₀ := by
      rw [← hcg, ← map_mul, hc', map_mul]
    rw [Subgroup.smul_def, smul_eq_mul]
    simp only [hF₂]
    congr 1
    rw [mul_inv_rev]
    calc y⁻¹ * (↑g)⁻¹ * globalPoints (𝓞 F) F γ₀ * (centralScalar (𝓞 F) F z * (↑g * y))
        = y⁻¹ * (↑g)⁻¹ * globalPoints (𝓞 F) F γ₀ * ((centralScalar (𝓞 F) F z * ↑g) * y) := by group
      _ = y⁻¹ * (↑g)⁻¹ * globalPoints (𝓞 F) F γ₀ * ((↑g * centralScalar (𝓞 F) F z) * y) := by
          rw [PccAlpha.centralScalar_comm F z (g : AdelicGL2 (𝓞 F) F)]
      _ = y⁻¹ * ((↑g)⁻¹ * (globalPoints (𝓞 F) F γ₀ * ↑g)) * (centralScalar (𝓞 F) F z * y) := by group
      _ = y⁻¹ * ((↑g)⁻¹ * (↑g * globalPoints (𝓞 F) F γ₀)) * (centralScalar (𝓞 F) F z * y) := by rw [hcomm]
      _ = _ := by group

  have hnorm : ∀ g : AdelicGL2 (𝓞 F) F, g ∈ Γ → k⁻¹ * g * k ∈ Γ ∧ k * g * k⁻¹ ∈ Γ := by
    intro g hg
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hg
    have hc' : γ₀ * c = c * γ₀ := (Subgroup.mem_centralizer_iff.mp hc) γ₀ (Set.mem_singleton γ₀)
    have h1 : h⁻¹ * γ₀ * h = S * γ₀ := hsh.symm
    constructor
    · refine Subgroup.mem_map.mpr ⟨h⁻¹ * c * h, ?_, by rw [map_mul, map_mul, map_inv]⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      have key : (h⁻¹ * γ₀ * h) * (h⁻¹ * c * h) = (h⁻¹ * c * h) * (h⁻¹ * γ₀ * h) := by
        calc (h⁻¹ * γ₀ * h) * (h⁻¹ * c * h) = h⁻¹ * (γ₀ * c) * h := by group
          _ = h⁻¹ * (c * γ₀) * h := by rw [hc']
          _ = _ := by group
      rw [h1] at key
      have key2 : S * (γ₀ * (h⁻¹ * c * h)) = S * (h⁻¹ * c * h * γ₀) := by
        calc S * (γ₀ * (h⁻¹ * c * h)) = S * γ₀ * (h⁻¹ * c * h) := by group
          _ = h⁻¹ * c * h * (S * γ₀) := key
          _ = h⁻¹ * c * h * S * γ₀ := by group
          _ = S * (h⁻¹ * c * h) * γ₀ := by rw [hSc (h⁻¹ * c * h)]
          _ = _ := by group
      exact mul_left_cancel key2
    · refine Subgroup.mem_map.mpr ⟨h * c * h⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]

      have h2 : γ₀ = h * (S * γ₀) * h⁻¹ := by rw [← h1]; group
      calc γ₀ * (h * c * h⁻¹) = h * (S * γ₀) * h⁻¹ * (h * c * h⁻¹) := by rw [← h2]
        _ = h * (S * (γ₀ * c)) * h⁻¹ := by group
        _ = h * (S * (c * γ₀)) * h⁻¹ := by rw [hc']
        _ = h * (c * S * γ₀) * h⁻¹ := by rw [← hSc c]; group
        _ = (h * c * h⁻¹) * (h * (S * γ₀) * h⁻¹) := by group
        _ = (h * c * h⁻¹) * γ₀ := by rw [← h2]

  have hqmp : Measure.QuasiMeasurePreserving (fun x => k⁻¹ * x) (μ.restrict B) (μ.restrict B) := by
    refine ⟨measurable_const_mul _, ?_⟩
    have : Measure.map (fun x => k⁻¹ * x) (μ.restrict B) = μ.restrict B := by
      ext s hs
      rw [Measure.map_apply (measurable_const_mul _) hs]
      exact PccAlpha.restrict_band_preimage_mul F α β k⁻¹ hkdet' s
    rw [this]
  let e : Γ ≃ Γ :=
    { toFun := fun g => ⟨k⁻¹ * g * k, (hnorm g g.2).1⟩
      invFun := fun g => ⟨k * g * k⁻¹, (hnorm g g.2).2⟩
      left_inv := fun g => Subtype.ext (by simp [mul_assoc])
      right_inv := fun g => Subtype.ext (by simp [mul_assoc]) }
  have hΨk : IsFundamentalDomain Γ ((fun x => k * x) '' Ψ) (μ.restrict B) := by
    have := hΨ.image_of_equiv (Equiv.mulLeft k) hqmp e (fun g x => ?_)
    · simpa using this
    · show k * ((k⁻¹ * (g : AdelicGL2 (𝓞 F) F) * k) * x) = (g : AdelicGL2 (𝓞 F) F) * (k * x)
      group

  have hΨks : (fun x => k * x) '' Ψ ⊆ B := by
    rintro _ ⟨x, hx, rfl⟩
    have := hΨs hx
    simp only [hB, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul, hkdet, one_mul] at this ⊢
    exact this

  haveI : Countable Γ := by
    haveI := PccAlpha.countable_GL2 F
    exact Function.Surjective.countable
      (f := fun c : Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F)) =>
        (⟨globalPoints (𝓞 F) F c, Subgroup.mem_map_of_mem _ c.2⟩ : Γ))
      (fun g => by
        obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp g.2
        exact ⟨⟨c, hc⟩, Subtype.ext hcg⟩)
  haveI : SMulInvariantMeasure Γ (AdelicGL2 (𝓞 F) F) (μ.restrict B) := by
    refine ⟨fun g s hs => ?_⟩
    obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp g.2
    have : (fun x => g • x) ⁻¹' s = (fun x => (g : AdelicGL2 (𝓞 F) F) * x) ⁻¹' s := rfl
    rw [this]
    exact PccAlpha.restrict_band_preimage_mul F α β _ (by rw [← hcg]; exact AutomorphicForm.ideleNorm_det_globalPoints c) s

  have hcov : ∫ x in Ψ, F₂ (k * x) ∂μ = ∫ y in (fun x => k * x) '' Ψ, F₂ y ∂μ := by
    have hm : Measure.map (MeasurableEquiv.mulLeft k) μ = μ := map_mul_left_eq_self μ k
    conv_rhs => rw [← hm]
    rw [setIntegral_map_equiv]
    simp only [MeasurableEquiv.coe_mulLeft]
    rw [Set.preimage_image_eq Ψ (mul_right_injective k)]
  rw [hcov, ← Measure.restrict_restrict_of_subset hΨks, ← Measure.restrict_restrict_of_subset hΨs]
  exact (hΨk.setIntegral_eq hΨ hF₂inv)

end S_AutomorphicForm_setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_of_scalar_mul_eq_conj
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_of_scalar_mul_eq_conj (solution)
