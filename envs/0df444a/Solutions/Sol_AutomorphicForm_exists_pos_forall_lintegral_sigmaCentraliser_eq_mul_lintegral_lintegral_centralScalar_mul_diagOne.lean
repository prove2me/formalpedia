-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_lintegral_sigmaCentraliser_eq_mul_lintegral_lintegral_centralScalar_mul_diagOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/7a55856d-fb01-5ea5-9ec4-bc2587b3a117

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_lintegral_sigmaCentraliser_eq_mul_lintegral_lintegral_centralScalar_mul_diagOne
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

namespace CPMA9

open AutomorphicForm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ)

theorem centralScalar_mem_center (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.centralScalar (𝓞 L) L z ∈ Subgroup.center (AdelicGL2 (𝓞 L) L) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨z, rfl⟩

noncomputable def Ψ : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ →* (AdelicGL2 (𝓞 L) L) where
  toFun p := AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    have hc := Subgroup.mem_center_iff.mp (centralScalar_mem_center L q.1) (diagOne (θ p.2))

    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, ← hc, mul_assoc]

theorem Ψ_apply (p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    Ψ K L θ p = AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2) := rfl

theorem Ψ_val (z : (AdeleRing (𝓞 L) L)ˣ) (a : (AdeleRing (𝓞 K) K)ˣ) :
    ((Ψ K L θ (z, a) : (AdelicGL2 (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      !![(z : (AdeleRing (𝓞 L) L)) * (θ a : (AdeleRing (𝓞 L) L)), 0; 0, (z : (AdeleRing (𝓞 L) L))] := by
  rw [Ψ_apply, Matrix.GeneralLinearGroup.coe_mul, NumberField.AdelicVolume.centralScalar_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply, Matrix.diagonal]

theorem Ψ_injective (hθi : Function.Injective θ) : Function.Injective (Ψ K L θ) := by
  intro p q hpq
  obtain ⟨z, a⟩ := p
  obtain ⟨z', a'⟩ := q
  have h := congrArg (fun g : (AdelicGL2 (𝓞 L) L) => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))) hpq
  simp only [Ψ_val] at h
  have h11 : (z : (AdeleRing (𝓞 L) L)) = z' := by
    have := congrFun (congrFun h 1) 1; simpa using this
  have h00 : (z : (AdeleRing (𝓞 L) L)) * (θ a : (AdeleRing (𝓞 L) L)) = z' * (θ a' : (AdeleRing (𝓞 L) L)) := by
    have := congrFun (congrFun h 0) 0; simpa using this
  have hz : z = z' := Units.ext h11
  subst hz
  have hθ : θ a = θ a' := by
    apply Units.ext
    have := congrArg (fun x : (AdeleRing (𝓞 L) L) => ((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : (AdeleRing (𝓞 L) L)) * x) h00
    simpa [← mul_assoc] using this
  exact Prod.ext rfl (hθi hθ)

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) =
      AutomorphicForm.centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  apply Units.ext
  ext i j
  rw [AutomorphicForm.sigmaAdelicAct, Matrix.GeneralLinearGroup.map_apply]
  by_cases hij : i = j
  · subst hij
    rw [NumberField.AdelicVolume.centralScalar_apply_eq, NumberField.AdelicVolume.centralScalar_apply_eq]
    rfl
  · rw [NumberField.AdelicVolume.centralScalar_apply_ne _ hij, NumberField.AdelicVolume.centralScalar_apply_ne _ hij,
      map_zero]

theorem sigmaAdelicAct_diagOne (u : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (diagOne u) = diagOne (D.unitsAct σ u) := by
  apply Units.ext
  ext i j
  rw [AutomorphicForm.sigmaAdelicAct, Matrix.GeneralLinearGroup.map_apply]
  show ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) ((diagOne u : Matrix (Fin 2) (Fin 2) _) i j) =
    (diagOne (D.unitsAct σ u) : Matrix (Fin 2) (Fin 2) _) i j
  rw [diagOne_coe_apply, diagOne_coe_apply]
  have hu : (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (u : AdeleRing (𝓞 L) L) =
      ((D.unitsAct σ u : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) := rfl
  fin_cases i <;> fin_cases j <;> simp [hu]

theorem sigmaAdelicAct_Ψ (hfix : ∀ a, D.unitsAct σ (θ a) = θ a)
    (z : (AdeleRing (𝓞 L) L)ˣ) (a : (AdeleRing (𝓞 K) K)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (Ψ K L θ (z, a)) = Ψ K L θ (D.unitsAct σ z, a) := by
  rw [Ψ_apply, Ψ_apply, map_mul, sigmaAdelicAct_centralScalar, sigmaAdelicAct_diagOne, hfix]

theorem Ψ_mem (H : Subgroup (AdelicGL2 (𝓞 L) L))
    (hH : ∀ h : (AdelicGL2 (𝓞 L) L), h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧ (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (hfix : ∀ a, D.unitsAct σ (θ a) = θ a)
    (z : (AdeleRing (𝓞 L) L)ˣ) (a : (AdeleRing (𝓞 K) K)ˣ) : Ψ K L θ (z, a) ∈ H := by
  rw [hH]
  refine ⟨by simp [Ψ_val], by simp [Ψ_val], ?_⟩
  rw [sigmaAdelicAct_Ψ K L D σ θ hfix]
  have : Ψ K L θ (D.unitsAct σ z, a) * (Ψ K L θ (z, a))⁻¹ = Ψ K L θ ((D.unitsAct σ z) * z⁻¹, 1) := by
    rw [← map_inv, ← map_mul]; congr 1; ext <;> simp
  rw [this, Ψ_apply]
  show AutomorphicForm.centralScalar (𝓞 L) L (D.unitsAct σ z * z⁻¹) * diagOne (θ 1) ∈ _
  rw [map_one, map_one, mul_one]
  exact centralScalar_mem_center L _

theorem exists_Ψ_eq (H : Subgroup (AdelicGL2 (𝓞 L) L))
    (hH : ∀ h : (AdelicGL2 (𝓞 L) L), h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧ (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (hθr : ∀ b : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ b = b → b ∈ Set.range θ)
    (h : (AdelicGL2 (𝓞 L) L)) (hh : h ∈ H) : ∃ p, Ψ K L θ p = h := by
  obtain ⟨h10, h01, hcen⟩ := (hH h).mp hh

  set M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L) := (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) with hM
  have hdet : IsUnit (M 0 0 * M 1 1) := by
    have : M.det = M 0 0 * M 1 1 := by rw [Matrix.det_fin_two, h10, h01]; ring
    rw [← this, hM]
    exact Matrix.isUnits_det_units h
  obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_left hdet
  obtain ⟨v, hv⟩ := isUnit_of_mul_isUnit_right hdet

  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen
  obtain ⟨w, hw⟩ := hcen
  have hσh : AutomorphicForm.sigmaAdelicAct K L D σ h = AutomorphicForm.centralScalar (𝓞 L) L w * h := by
    show _ = Matrix.GeneralLinearGroup.scalar (Fin 2) w * h
    rw [hw, inv_mul_cancel_right]
  have hent : ∀ i : Fin 2, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (M i i) = (w : AdeleRing (𝓞 L) L) * M i i := by
    have key : ∀ i : Fin 2, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (M i i) =
        ∑ j : Fin 2, ((AutomorphicForm.centralScalar (𝓞 L) L w : AdelicGL2 (𝓞 L) L) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j * M j i := by
      intro i
      have h1 := congrArg (fun g : (AdelicGL2 (𝓞 L) L) => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i i) hσh
      beta_reduce at h1
      rw [AutomorphicForm.sigmaAdelicAct, Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.mul_apply] at h1
      exact h1
    intro i
    rw [key i, Fin.sum_univ_two, NumberField.AdelicVolume.centralScalar_val]
    have hM10 : M 1 0 = 0 := h10
    have hM01 : M 0 1 = 0 := h01
    fin_cases i <;> simp [Matrix.diagonal, hM10, hM01]
  have hσu : D.unitsAct σ u = w * u := by
    apply Units.ext
    show (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (u : AdeleRing (𝓞 L) L) = (w : AdeleRing (𝓞 L) L) * u
    rw [hu]; exact hent 0
  have hσv : D.unitsAct σ v = w * v := by
    apply Units.ext
    show (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (v : AdeleRing (𝓞 L) L) = (w : AdeleRing (𝓞 L) L) * v
    rw [hv]; exact hent 1
  have hfixuv : D.unitsAct σ (u * v⁻¹) = u * v⁻¹ := by
    rw [map_mul, map_inv, hσu, hσv, mul_comm w u, mul_inv_rev, mul_assoc, mul_comm v⁻¹ w⁻¹,
      mul_inv_cancel_left]
  obtain ⟨a, ha⟩ := hθr _ hfixuv
  refine ⟨(v, a), ?_⟩
  apply Units.ext
  rw [Ψ_val, ha]
  ext i j
  fin_cases i <;> fin_cases j
  · show (v : AdeleRing (𝓞 L) L) * ((u * v⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = M 0 0
    rw [← hu, Units.val_mul, ← mul_assoc, mul_comm (v : AdeleRing (𝓞 L) L), mul_assoc, Units.mul_inv, mul_one]
  · show (0 : AdeleRing (𝓞 L) L) = M 0 1
    rw [h01]
  · show (0 : AdeleRing (𝓞 L) L) = M 1 0
    rw [h10]
  · show (v : AdeleRing (𝓞 L) L) = M 1 1
    rw [hv]

end CPMA9

namespace CPMA9

open AutomorphicForm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ)

omit [NumberField K] in
theorem continuous_toGL {X : Type*} [TopologicalSpace X] {f : X → AdelicGL2 (𝓞 L) L}
    (h1 : ∀ i j : Fin 2, Continuous fun x => ((f x : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j)
    (h2 : ∀ i j : Fin 2, Continuous fun x => (((f x)⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) :
    Continuous f :=
  Units.continuous_iff.mpr ⟨continuous_matrix h1, continuous_matrix h2⟩

omit [NumberField K] in
theorem continuous_centralScalar : Continuous (AutomorphicForm.centralScalar (𝓞 L) L) := by
  apply continuous_toGL
  · intro i j
    by_cases hij : i = j
    · subst hij
      simp only [NumberField.AdelicVolume.centralScalar_apply_eq]
      exact Units.continuous_val
    · simp only [NumberField.AdelicVolume.centralScalar_apply_ne _ hij]
      exact continuous_const
  · intro i j
    simp only [← map_inv]
    by_cases hij : i = j
    · subst hij
      simp only [NumberField.AdelicVolume.centralScalar_apply_eq]
      exact Units.continuous_coe_inv
    · simp only [NumberField.AdelicVolume.centralScalar_apply_ne _ hij]
      exact continuous_const

omit [NumberField K] in
theorem continuous_diagOne' : Continuous (diagOne : (AdeleRing (𝓞 L) L)ˣ → AdelicGL2 (𝓞 L) L) := by
  apply continuous_toGL
  · intro i j
    simp only [diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> first
      | exact Units.continuous_val | exact continuous_const
  · intro i j
    simp only [← map_inv, diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> first
      | exact Units.continuous_coe_inv | exact continuous_const

theorem continuous_Ψ (hθ : Continuous θ) : Continuous (Ψ K L θ) := by
  show Continuous fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ =>
    AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)
  exact ((continuous_centralScalar L).comp continuous_fst).mul
    ((continuous_diagOne' L).comp (hθ.comp continuous_snd))

end CPMA9

attribute [local instance] NumberField.AdelicHaar.glBorel

open CPMA9 AutomorphicForm in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure]
    (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ) (hθ : Continuous θ) (hθi : Function.Injective θ)
    (hθn : ∀ a, NumberField.TateGlobal.ideleNorm L (θ a) = NumberField.TateGlobal.ideleNorm K a ^ Module.finrank K L)
    (hθc : ∀ k : Kˣ, θ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (algebraMap K L : K →* L) k))
    (hθr : ∀ b : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ b = b ↔ b ∈ Set.range θ) :
    ∃ cH : ℝ, 0 < cH ∧ ∀ f : AdelicGL2 (𝓞 L) L → ENNReal, Measurable f →
      ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂μH =
        ENNReal.ofReal cH * ∫⁻ z, ∫⁻ a, f (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)) ∂νK ∂νZL := by
  classical

  haveI : SecondCountableTopology (AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ :=
    (NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box K L).1
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ :=
    (NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box K K).1
  haveI hHlc : LocallyCompactSpace H := hHc.locallyCompactSpace
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace H := Subtype.borelSpace _
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : MeasurableMul (AdeleRing (𝓞 L) L)ˣ := by infer_instance
  haveI : MeasurableMul (AdeleRing (𝓞 K) K)ˣ := by infer_instance
  haveI : SigmaFinite νZL := by infer_instance
  haveI : SigmaFinite νK := by infer_instance
  haveI : (νZL.prod νK).IsHaarMeasure := Measure.prod.instIsHaarMeasure νZL νK

  have hfix : ∀ a, D.unitsAct σ (θ a) = θ a := fun a => (hθr (θ a)).mpr ⟨a, rfl⟩
  have hran : ∀ b : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ b = b → b ∈ Set.range θ := fun b hb => (hθr b).mp hb

  let Ψ' : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ →* H :=
    (Ψ K L θ).codRestrict H fun p => Ψ_mem K L D σ θ H hH hfix p.1 p.2
  have hΨ'c : Continuous Ψ' := (continuous_Ψ K L θ hθ).subtype_mk _
  have hΨ'bij : Function.Bijective Ψ' := by
    refine ⟨fun p q hpq => Ψ_injective K L θ hθi (congrArg Subtype.val hpq), fun h => ?_⟩
    obtain ⟨p, hp⟩ := exists_Ψ_eq K L D σ θ H hH hran h.1 h.2
    exact ⟨p, Subtype.ext hp⟩
  have hopen : IsOpenMap Ψ' := MonoidHom.isOpenMap_of_sigmaCompact Ψ' hΨ'bij.2 hΨ'c
  let eqv : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ H := Equiv.ofBijective Ψ' hΨ'bij
  let hom : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ₜ H := eqv.toHomeomorphOfContinuousOpen hΨ'c hopen
  let e : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ₜ* H :=
    { MulEquiv.ofBijective Ψ' hΨ'bij with
      continuous_toFun := hΨ'c
      continuous_invFun := hom.continuous_symm }
  have he : ∀ p, ((e p : H) : AdelicGL2 (𝓞 L) L) = Ψ K L θ p := fun p => rfl

  let μ0 : Measure H := (νZL.prod νK).map e
  haveI : μ0.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map (νZL.prod νK) e
  have huniq : μH = μH.haarScalarFactor μ0 • μ0 := Measure.isMulLeftInvariant_eq_smul μH μ0
  set c : NNReal := μH.haarScalarFactor μ0 with hc
  have hcpos : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure μH μ0
  refine ⟨c, by exact_mod_cast hcpos, fun f hf => ?_⟩
  have hfe : Measurable fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ => f (Ψ K L θ p) :=
    hf.comp (continuous_Ψ K L θ hθ).measurable
  calc ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂μH
      = ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂(c • μ0) := by rw [← huniq]
    _ = c * ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂μ0 := by
        rw [lintegral_smul_measure]; rfl
    _ = c * ∫⁻ p, f (Ψ K L θ p) ∂(νZL.prod νK) := by
        congr 1
        have hem : Measurable (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ => e p) := hΨ'c.measurable
        have hfm : Measurable (fun h : H => f (h : AdelicGL2 (𝓞 L) L)) := hf.comp measurable_subtype_coe
        show ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂(Measure.map (fun p => e p) (νZL.prod νK)) = _
        rw [lintegral_map hfm hem]
        rfl
    _ = c * ∫⁻ z, ∫⁻ a, f (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)) ∂νK ∂νZL := by
        congr 1
        rw [lintegral_prod _ hfe.aemeasurable]
        rfl
    _ = ENNReal.ofReal (c : ℝ) * ∫⁻ z, ∫⁻ a, f (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)) ∂νK ∂νZL := by
        rw [ENNReal.ofReal_coe_nnreal]

end S_AutomorphicForm_exists_pos_forall_lintegral_sigmaCentraliser_eq_mul_lintegral_lintegral_centralScalar_mul_diagOne
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_lintegral_sigmaCentraliser_eq_mul_lintegral_lintegral_centralScalar_mul_diagOne (solution)
