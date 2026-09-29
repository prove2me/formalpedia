-- Prove2me | solution 1 for AutomorphicForm.forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2_of_forall_lintegral_eq_idelesBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/021a7647-1e1a-5805-abf1-51ed95cb90b1

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
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2_of_forall_lintegral_eq_idelesBaseChange
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

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

namespace FDT

open AutomorphicForm CPMA9

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem subgroup_eq_top_of_measure_compl_eq_zero {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (hμ : μ Set.univ ≠ 0)
    (S : Subgroup G) (hS : μ (S : Set G)ᶜ = 0) : S = ⊤ := by
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ S := by
    by_contra h
    push_neg at h
    exact hne ((Subgroup.eq_top_iff' S).mpr h)
  have hsub : (fun x => g⁻¹ * x) ⁻¹' (S : Set G) ⊆ (S : Set G)ᶜ := by
    intro x hx hxS
    apply hg
    have h1 : g⁻¹ * x ∈ S := hx
    have h2 : g⁻¹ ∈ S := by
      have := S.mul_mem h1 (S.inv_mem hxS)
      rwa [mul_inv_cancel_right] at this
    exact inv_mem_iff.mp h2
  have hS0 : μ (S : Set G) = 0 := by
    rw [← measure_preimage_mul μ g⁻¹ (S : Set G)]
    exact measure_mono_null hsub hS
  apply hμ
  rw [← Set.union_compl_self (S : Set G)]
  exact measure_union_null hS0 hS

theorem measurableSet_of_isSigmaCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {s : Set X} (hs : IsSigmaCompact s) :
    MeasurableSet s := by
  obtain ⟨C, hC, rfl⟩ := hs
  exact MeasurableSet.iUnion fun n => (hC n).isClosed.measurableSet

open scoped TensorProduct.RightActions in

theorem exists_equiv
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure]
    (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ) (hθ : Continuous θ) (hθi : Function.Injective θ)
    (cH : ℝ) (hcH : 0 < cH)
    (hμH : ∀ f : AdelicGL2 (𝓞 L) L → ENNReal, Measurable f →
      ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂μH =
        ENNReal.ofReal cH * ∫⁻ z, ∫⁻ a, f (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)) ∂νK ∂νZL) :
    ∃ e : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ₜ* H,
      (∀ p, ((e p : H) : AdelicGL2 (𝓞 L) L) = Ψ K L θ p) ∧
      μH = ENNReal.ofReal cH • Measure.map e (νZL.prod νK) := by
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
  haveI : MeasurableMul ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) := by infer_instance
  haveI : MeasurableMul H := by infer_instance
  haveI : SigmaFinite νZL := by infer_instance
  haveI : SigmaFinite νK := by infer_instance
  haveI : (νZL.prod νK).IsHaarMeasure := Measure.prod.instIsHaarMeasure νZL νK
  set ν : Measure ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) := νZL.prod νK with hν
  have hΨc : Continuous (Ψ K L θ) := continuous_Ψ K L θ hθ
  have hΨm : Measurable (Ψ K L θ) := hΨc.measurable
  have hHm : MeasurableSet (H : Set (AdelicGL2 (𝓞 L) L)) := hHc.measurableSet
  have hc0 : ENNReal.ofReal cH ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hcH

  have hmapG : Measure.map (Subtype.val : H → AdelicGL2 (𝓞 L) L) μH =
      ENNReal.ofReal cH • Measure.map (Ψ K L θ) ν := by
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    rw [lintegral_map hf measurable_subtype_coe, lintegral_smul_measure, lintegral_map hf hΨm, hμH f hf,
      smul_eq_mul, hν, lintegral_prod (fun p => f (Ψ K L θ p)) (hf.comp hΨm).aemeasurable]
    rfl
  have hpre : ∀ A : Set (AdelicGL2 (𝓞 L) L), MeasurableSet A →
      μH ((Subtype.val : H → AdelicGL2 (𝓞 L) L) ⁻¹' A) = ENNReal.ofReal cH * ν (Ψ K L θ ⁻¹' A) := by
    intro A hA
    rw [← Measure.map_apply measurable_subtype_coe hA, hmapG, Measure.smul_apply, Measure.map_apply hΨm hA,
      smul_eq_mul]

  have hmem : ∀ p, Ψ K L θ p ∈ H := by
    have h1 : ν (H.comap (Ψ K L θ) : Set ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ))ᶜ = 0 := by
      have h2 := hpre (H : Set (AdelicGL2 (𝓞 L) L))ᶜ hHm.compl
      rw [Set.preimage_compl, show (Subtype.val : H → AdelicGL2 (𝓞 L) L) ⁻¹' (H : Set (AdelicGL2 (𝓞 L) L))
          = Set.univ from Set.eq_univ_of_forall fun h => h.2, Set.compl_univ, measure_empty] at h2
      have h3 := (mul_eq_zero.mp h2.symm).resolve_left hc0
      rwa [Subgroup.coe_comap, ← Set.preimage_compl]
    have htop := subgroup_eq_top_of_measure_compl_eq_zero ν
      (isOpen_univ.measure_ne_zero ν Set.univ_nonempty) _ h1
    intro p
    have hp : p ∈ (⊤ : Subgroup ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ)) := Subgroup.mem_top p
    rw [← htop] at hp
    exact Subgroup.mem_comap.mp hp

  let Ψ' : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) →* H := (Ψ K L θ).codRestrict H hmem
  have hΨ'c : Continuous Ψ' := hΨc.subtype_mk _
  have hsurj : Function.Surjective Ψ' := by
    have hRm : MeasurableSet (Set.range (Ψ K L θ)) :=
      measurableSet_of_isSigmaCompact (isSigmaCompact_range hΨc)
    have h1 : μH (Ψ'.range : Set H)ᶜ = 0 := by
      have hR : (Ψ'.range : Set H) = (Subtype.val : H → AdelicGL2 (𝓞 L) L) ⁻¹' Set.range (Ψ K L θ) := by
        ext h
        simp only [MonoidHom.coe_range, Set.mem_range, Set.mem_preimage]
        constructor
        · rintro ⟨p, rfl⟩
          exact ⟨p, rfl⟩
        · rintro ⟨p, hp⟩
          exact ⟨p, Subtype.ext hp⟩
      rw [hR, ← Set.preimage_compl, hpre _ hRm.compl, Set.preimage_compl,
        show Ψ K L θ ⁻¹' Set.range (Ψ K L θ) = Set.univ from Set.eq_univ_of_forall fun p => ⟨p, rfl⟩,
        Set.compl_univ, measure_empty, mul_zero]
    have htop := subgroup_eq_top_of_measure_compl_eq_zero μH
      (isOpen_univ.measure_ne_zero μH Set.univ_nonempty) _ h1
    exact MonoidHom.range_eq_top.mp htop

  have hΨ'bij : Function.Bijective Ψ' :=
    ⟨fun p q hpq => Ψ_injective K L θ hθi (congrArg Subtype.val hpq), hsurj⟩
  have hopen : IsOpenMap Ψ' := MonoidHom.isOpenMap_of_sigmaCompact Ψ' hsurj hΨ'c
  let eqv : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ H := Equiv.ofBijective Ψ' hΨ'bij
  let hom : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ₜ H := eqv.toHomeomorphOfContinuousOpen hΨ'c hopen
  let e : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ₜ* H :=
    { MulEquiv.ofBijective Ψ' hΨ'bij with
      continuous_toFun := hΨ'c
      continuous_invFun := hom.continuous_symm }
  have he : ∀ p, ((e p : H) : AdelicGL2 (𝓞 L) L) = Ψ K L θ p := fun p => rfl
  refine ⟨e, he, ?_⟩

  have hem : Measurable (e : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) → H) := e.continuous.measurable
  have hvalemb : MeasurableEmbedding (Subtype.val : H → AdelicGL2 (𝓞 L) L) :=
    MeasurableEmbedding.subtype_coe hHm
  refine Measure.ext fun S hS => ?_
  rw [Measure.smul_apply, Measure.map_apply hem hS, smul_eq_mul]
  have hS' : MeasurableSet (Subtype.val '' S) := hvalemb.measurableSet_image' hS
  have h1 : (Subtype.val : H → AdelicGL2 (𝓞 L) L) ⁻¹' (Subtype.val '' S) = S :=
    Set.preimage_image_eq S Subtype.val_injective
  have h2 : Ψ K L θ ⁻¹' (Subtype.val '' S) = e ⁻¹' S := by
    ext p
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨h, hh, hhp⟩
      have : h = e p := Subtype.ext (hhp.trans (he p).symm)
      exact this ▸ hh
    · intro hp
      exact ⟨e p, hp, he p⟩
  rw [← h2, ← hpre _ hS', h1]

section transport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (μH : Measure H)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    (cH : ℝ) (hcH : 0 < cH)
    (e : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ₜ* H)
    (hμ : μH = ENNReal.ofReal cH • Measure.map e (νZL.prod νK))

theorem exists_measurableEquiv :
    ∃ em : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ᵐ H, (em : _ → H) = e := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ :=
    (NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box K L).1
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ :=
    (NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box K K).1
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace H := Subtype.borelSpace _
  exact ⟨e.toHomeomorph.toMeasurableEquiv, rfl⟩

include hcH in
theorem ofReal_cH_ne_zero : ENNReal.ofReal cH ≠ 0 := by
  rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hcH

include hμ in

theorem setLIntegral_eq_mul (S : Set H) (g : H → ENNReal) :
    ∫⁻ h in S, g h ∂μH = ENNReal.ofReal cH * ∫⁻ p in e ⁻¹' S, g (e p) ∂(νZL.prod νK) := by
  obtain ⟨em, hem⟩ := exists_measurableEquiv K L H e
  rw [hμ, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← hem, MeasurableEquiv.restrict_map,
    lintegral_map_equiv]

include hcH hμ in

theorem integrableOn_iff (S : Set H) (g : H → ℂ) :
    IntegrableOn g S μH ↔ IntegrableOn (fun p => g (e p)) (e ⁻¹' S) (νZL.prod νK) := by
  obtain ⟨em, hem⟩ := exists_measurableEquiv K L H e
  rw [hμ, IntegrableOn, Measure.restrict_smul,
    integrable_smul_measure (ofReal_cH_ne_zero cH hcH) ENNReal.ofReal_ne_top, ← hem]
  exact integrableOn_map_equiv em

include hcH hμ in

theorem setIntegral_eq_mul (S : Set H) (g : H → ℂ) :
    ∫ h in S, g h ∂μH = (cH : ℂ) * ∫ p in e ⁻¹' S, g (e p) ∂(νZL.prod νK) := by
  obtain ⟨em, hem⟩ := exists_measurableEquiv K L H e
  rw [hμ, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hcH.le, ← hem,
    setIntegral_map_equiv, Complex.real_smul]

include hcH hμ in

theorem quasiMeasurePreserving : Measure.QuasiMeasurePreserving e (νZL.prod νK) μH := by
  obtain ⟨em, hem⟩ := exists_measurableEquiv K L H e
  refine ⟨hem ▸ em.measurable, ?_⟩
  rw [hμ]
  refine Measure.AbsolutelyContinuous.mk fun s _ hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hs
  exact hs.resolve_left (ofReal_cH_ne_zero cH hcH)

include hμ in

theorem quasiMeasurePreserving_symm : Measure.QuasiMeasurePreserving e.symm μH (νZL.prod νK) := by
  obtain ⟨em, hem⟩ := exists_measurableEquiv K L H e
  have hsm : (em.symm : H → _) = e.symm := by
    funext h
    apply em.injective
    rw [em.apply_symm_apply, hem, ContinuousMulEquiv.apply_symm_apply]
  refine ⟨hsm ▸ em.symm.measurable, ?_⟩
  rw [hμ, Measure.map_smul, ← hem, ← hsm, MeasurableEquiv.map_symm_map]
  exact Measure.smul_absolutelyContinuous

end transport

open scoped TensorProduct.RightActions in

theorem preimage_setOf_eq_prod_and_eq_image
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (H : Subgroup (AdelicGL2 (𝓞 L) L))
    (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ) (hθi : Function.Injective θ)
    (e : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ₜ* H)
    (he : ∀ p, ((e p : H) : AdelicGL2 (𝓞 L) L) = Ψ K L θ p)
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ) (ΩK : Set (AdeleRing (𝓞 K) K)ˣ) :
    e ⁻¹' {h : H | ∃ z ∈ ΩL, ∃ a ∈ ΩK,
        (h : AdelicGL2 (𝓞 L) L) = AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)} = ΩL ×ˢ ΩK ∧
    {h : H | ∃ z ∈ ΩL, ∃ a ∈ ΩK,
        (h : AdelicGL2 (𝓞 L) L) = AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)} = e '' (ΩL ×ˢ ΩK) := by
  have h1 : e ⁻¹' {h : H | ∃ z ∈ ΩL, ∃ a ∈ ΩK,
      (h : AdelicGL2 (𝓞 L) L) = AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)} = ΩL ×ˢ ΩK := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq, he, Set.mem_prod]
    constructor
    · rintro ⟨z, hz, a, ha, hzap⟩
      have : p = (z, a) := Ψ_injective K L θ hθi (hzap.trans (Ψ_apply K L θ (z, a)).symm)
      subst this
      exact ⟨hz, ha⟩
    · rintro ⟨hz, ha⟩
      exact ⟨p.1, hz, p.2, ha, Ψ_apply K L θ p⟩
  refine ⟨h1, ?_⟩
  rw [← h1, Set.image_preimage_eq _ e.surjective]

end FDT

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure]
    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (cH : ℝ) (hcH : 0 < cH)
    (hμH : ∀ f : AdelicGL2 (𝓞 L) L → ENNReal, Measurable f →
      ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂μH =
        ENNReal.ofReal cH * ∫⁻ z, ∫⁻ a, f (AutomorphicForm.centralScalar (𝓞 L) L z *
          diagOne ((Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom) a)) ∂νK ∂νZL) :
    ∀ g : AdelicGL2 (𝓞 L) L → ℂ,
      ∫ h : H, g (h : AdelicGL2 (𝓞 L) L) ∂μH =
        cH * ∫ p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 L) L p.1 *
            AutomorphicForm.baseChangeGL K L
              (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.2 1))) ∂(νZL.prod νK)  := by
  intro g
  have hθc : Continuous (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom :
      (AdeleRing (𝓞 K) K)ˣ → (AdeleRing (𝓞 L) L)ˣ) :=
    Continuous.units_map _ (M4aHerbrand.Bridge.continuous_genuineβ K L)
  have hθi : Function.Injective (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom :
      (AdeleRing (𝓞 K) K)ˣ → (AdeleRing (𝓞 L) L)ˣ) := by
    intro a b h
    apply Units.ext
    have h' := congrArg (fun u : (AdeleRing (𝓞 L) L)ˣ => (u : AdeleRing (𝓞 L) L)) h
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h'
    have e : ∀ x : AdeleRing (𝓞 K) K, (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β x =
        AutomorphicForm.baseChangeEquiv K L ((1 : L) ⊗ₜ[K] x) :=
      fun x => (AutomorphicForm.baseChangeEquiv_one_tmul K L x).symm
    rw [e, e] at h'
    have h'' := (AutomorphicForm.baseChangeEquiv K L).injective h'
    exact Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective h''
  obtain ⟨e, he, hμ⟩ := FDT.exists_equiv K L H hHc μH νZL νK _ hθc hθi cH hcH hμH
  obtain ⟨em, hem⟩ := FDT.exists_measurableEquiv K L H e
  rw [hμ, integral_smul_measure, ← hem, integral_map_equiv, ENNReal.toReal_ofReal hcH.le, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have hep : (em p : H) = e p := congrFun hem p
  simp only [hep, he p, CPMA9.Ψ_apply]
  congr 1
  congr 1
  apply Units.ext
  ext i j
  rw [diagOne_coe_apply]
  change _ = AutomorphicForm.baseChangeEquiv K L
    ((Algebra.TensorProduct.includeRight : AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K)
      (((diagUnits2 p.2 1 : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j))
  rw [Algebra.TensorProduct.includeRight_apply, AutomorphicForm.baseChangeEquiv_one_tmul]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, diagUnits2]
  rfl

end S_AutomorphicForm_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2_of_forall_lintegral_eq_idelesBaseChange
end P2MW
export P2MW.S_AutomorphicForm_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2_of_forall_lintegral_eq_idelesBaseChange (solution)
