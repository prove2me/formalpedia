-- Prove2me | solution 1 for AutomorphicForm.isFundamentalDomain_image_and_forall_setLIntegral_torusShell_eq_mul_setLIntegral_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/913a912b-af13-5703-95d9-d2c4bb70a4e0

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
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isFundamentalDomain_image_and_forall_setLIntegral_torusShell_eq_mul_setLIntegral_prod
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

namespace FDTA9

open AutomorphicForm

section ProdFD

variable {A B : Type*} [Group A] [Group B] [MeasurableSpace A] [MeasurableSpace B]
  (RA : Subgroup A) (RB : Subgroup B)

theorem smul_prod_eq (δ : ↥(RA.prod RB)) (s : Set A) (t : Set B) :
    (δ • (s ×ˢ t) : Set (A × B)) = ((⟨δ.1.1, (Subgroup.mem_prod.mp δ.2).1⟩ : ↥RA) • s) ×ˢ
      ((⟨δ.1.2, (Subgroup.mem_prod.mp δ.2).2⟩ : ↥RB) • t) := by
  ext ⟨a, b⟩
  simp only [Set.mem_smul_set, Set.mem_prod]
  constructor
  · rintro ⟨⟨a', b'⟩, ⟨ha', hb'⟩, h⟩
    have h1 : δ.1.1 * a' = a := congrArg Prod.fst h
    have h2 : δ.1.2 * b' = b := congrArg Prod.snd h
    exact ⟨⟨a', ha', h1⟩, ⟨b', hb', h2⟩⟩
  · rintro ⟨⟨a', ha', h1⟩, ⟨b', hb', h2⟩⟩
    exact ⟨(a', b'), ⟨ha', hb'⟩, Prod.ext h1 h2⟩

theorem isFundamentalDomain_prod (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    {s : Set A} {t : Set B} (hs : IsFundamentalDomain (↥RA) s μ) (ht : IsFundamentalDomain (↥RB) t ν) :
    IsFundamentalDomain (↥(RA.prod RB)) (s ×ˢ t) (μ.prod ν) where
  nullMeasurableSet := hs.nullMeasurableSet.prod ht.nullMeasurableSet
  ae_covers := by
    have h1 : ∀ᵐ p : A × B ∂μ.prod ν, ∃ g : ↥RA, g • p.1 ∈ s :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 : ∀ᵐ p : A × B ∂μ.prod ν, ∃ g : ↥RB, g • p.2 ∈ t :=
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p h1 h2
    obtain ⟨g, hg⟩ := h1
    obtain ⟨h, hh⟩ := h2
    exact ⟨⟨(g.1, h.1), Subgroup.mem_prod.mpr ⟨g.2, h.2⟩⟩, ⟨hg, hh⟩⟩
  aedisjoint := by
    intro δ δ' hne
    change (μ.prod ν) (δ • (s ×ˢ t) ∩ δ' • (s ×ˢ t)) = 0
    rw [smul_prod_eq, smul_prod_eq, Set.prod_inter_prod, Measure.prod_prod]
    by_cases h1 : δ.1.1 = δ'.1.1
    · have h2 : (⟨δ.1.2, (Subgroup.mem_prod.mp δ.2).2⟩ : ↥RB) ≠ ⟨δ'.1.2, (Subgroup.mem_prod.mp δ'.2).2⟩ := by
        intro h
        apply hne
        exact Subtype.ext (Prod.ext h1 (congrArg Subtype.val h))
      have := ht.aedisjoint h2
      change ν (_ ∩ _) = 0 at this
      rw [this, mul_zero]
    · have h2 : (⟨δ.1.1, (Subgroup.mem_prod.mp δ.2).1⟩ : ↥RA) ≠ ⟨δ'.1.1, (Subgroup.mem_prod.mp δ'.2).1⟩ :=
        fun h => h1 (congrArg Subtype.val h)
      have := hs.aedisjoint h2
      change μ (_ ∩ _) = 0 at this
      rw [this, zero_mul]

end ProdFD

section Transport

variable {P Q : Type*} [MeasurableSpace P] [MeasurableSpace Q] (em : P ≃ᵐ Q)
  (ν : Measure P) (μ : Measure Q) (c : ℝ) (hc : 0 < c) (hμ : μ = ENNReal.ofReal c • Measure.map em ν)

include hμ in
theorem restrict_eq (S : Set P) : μ.restrict (em '' S) = ENNReal.ofReal c • Measure.map em (ν.restrict S) := by
  rw [hμ, Measure.restrict_smul, MeasurableEquiv.restrict_map, em.preimage_image]

include hμ in
private theorem _root_.FDTA9.setLIntegral_eq (S : Set P) (F : Q → ENNReal) :
    ∫⁻ q in em '' S, F q ∂μ = ENNReal.ofReal c * ∫⁻ p in S, F (em p) ∂ν := by
  rw [restrict_eq em ν μ c hμ S, lintegral_smul_measure, lintegral_map_equiv, smul_eq_mul]

p2m_export "FDTA9" "setLIntegral_eq"
include hμ hc in
private theorem _root_.FDTA9.integrableOn_iff (S : Set P) (F : Q → ℂ) :
    IntegrableOn F (em '' S) μ ↔ IntegrableOn (fun p => F (em p)) S ν := by
  unfold IntegrableOn
  rw [restrict_eq em ν μ c hμ S, integrable_smul_measure (by simp [hc.ne', ENNReal.ofReal_eq_zero, not_le.mpr hc])
    ENNReal.ofReal_ne_top, integrable_map_equiv]
  rfl

p2m_export "FDTA9" "integrableOn_iff"
include hμ hc in
private theorem _root_.FDTA9.setIntegral_eq (S : Set P) (F : Q → ℂ) :
    ∫ q in em '' S, F q ∂μ = (c : ℂ) * ∫ p in S, F (em p) ∂ν := by
  rw [restrict_eq em ν μ c hμ S, integral_smul_measure, integral_map_equiv, ENNReal.toReal_ofReal hc.le,
    RCLike.real_smul_eq_coe_mul]
  rfl

p2m_export "FDTA9" "setIntegral_eq"
end Transport

end FDTA9

namespace FDTA9

open AutomorphicForm

theorem val_scalar_mul_diagOne {A : Type*} [CommRing A] (u v : Aˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagOne v : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      !![(u : A) * (v : A), 0; 0, (u : A)] := by
  rw [Matrix.GeneralLinearGroup.coe_mul]
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.diagonal fun _ => (u : A) := by
    show Matrix.scalar (Fin 2) (u : A) = _
    rw [Matrix.scalar_apply]
  rw [hs]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply, Matrix.diagonal]

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ)

noncomputable def lam (q : Lˣ) (k : Kˣ) : GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) q * diagOne (Units.map (algebraMap K L : K →* L) k)

omit [NumberField K] [NumberField L] in
theorem lam_val (q : Lˣ) (k : Kˣ) :
    ((lam K L q k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![(q : L) * algebraMap K L k, 0; 0, (q : L)] := by
  rw [lam, val_scalar_mul_diagOne]; rfl

theorem globalPoints_lam
    (hθc : ∀ k : Kˣ, θ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (algebraMap K L : K →* L) k))
    (q : Lˣ) (k : Kˣ) :
    globalPoints (𝓞 L) L (lam K L q k) =
      CPMA9.Ψ K L θ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q,
        Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) := by
  apply Units.ext
  rw [CPMA9.Ψ_val, hθc]
  ext i j
  show algebraMap L (AdeleRing (𝓞 L) L) (((lam K L q k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j) = _
  rw [lam_val]
  fin_cases i <;> fin_cases j <;> simp

omit [NumberField K] [NumberField L] in
theorem lam_mem (Λ₀ : Subgroup (GL (Fin 2) L))
    (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    (q : Lˣ) (k : Kˣ) : lam K L q k ∈ Λ₀ := by
  rw [hΛ₀, lam_val]
  refine ⟨by simp, by simp, ⟨(k : K), ?_⟩⟩
  simp [mul_div_cancel_left₀ _ q.ne_zero]

omit [NumberField K] [NumberField L] in
theorem exists_lam_eq (Λ₀ : Subgroup (GL (Fin 2) L))
    (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    (γ : GL (Fin 2) L) (hγ : γ ∈ Λ₀) : ∃ (q : Lˣ) (k : Kˣ), lam K L q k = γ := by
  obtain ⟨h10, h01, ⟨k, hk⟩⟩ := (hΛ₀ γ).mp hγ
  set M : Matrix (Fin 2) (Fin 2) L := (γ : Matrix (Fin 2) (Fin 2) L) with hM
  have hdet : M 0 0 * M 1 1 ≠ 0 := by
    have : M.det = M 0 0 * M 1 1 := by rw [Matrix.det_fin_two, h10, h01]; ring
    rw [← this, hM]
    exact (Matrix.isUnits_det_units γ).ne_zero
  have h00 : M 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have h11 : M 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have hk0 : k ≠ 0 := by
    intro h0; rw [h0, map_zero] at hk
    exact div_ne_zero h00 h11 hk.symm
  refine ⟨Units.mk0 (M 1 1) h11, Units.mk0 k hk0, ?_⟩
  apply Units.ext
  rw [lam_val]
  ext i j
  fin_cases i <;> fin_cases j
  · show M 1 1 * algebraMap K L k = M 0 0
    rw [hk, mul_div_cancel₀ _ h11]
  · show (0 : L) = M 0 1
    rw [h01]
  · show (0 : L) = M 1 0
    rw [h10]
  · rfl

omit [NumberField K] in
theorem gl2Weyl_conj_apply_one_zero (γ : GL (Fin 2) L) (h01 : (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) :
    ((gl2Weyl * γ * gl2Weyl⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  have hw : ((gl2Weyl : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![0, 1; 1, 0] := rfl
  have hwi : ((gl2Weyl⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![0, 1; 1, 0] := rfl
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hw, hwi]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, h01]

theorem integrand_invariant (α β : ℝ) (y : AdelicGL2 (𝓞 L) L) (R : ℝ)
    (γ : GL (Fin 2) L) (h10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (g : AdelicGL2 (𝓞 L) L) :
    (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
        (fun _ => (1 : ℂ)) (globalPoints (𝓞 L) L γ * g * y) *
      ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
          (fun _ => (1 : ℂ)) (globalPoints (𝓞 L) L γ * g * y)
        - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
            Real.exp R < NumberField.AdelicHeight.adelicHeight L (adelicWeyl (𝓞 L) L * y')}
          (fun _ => (1 : ℂ)) (globalPoints (𝓞 L) L γ * g * y))) =
    (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
        (fun _ => (1 : ℂ)) (g * y) *
      ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
          (fun _ => (1 : ℂ)) (g * y)
        - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
            Real.exp R < NumberField.AdelicHeight.adelicHeight L (adelicWeyl (𝓞 L) L * y')}
          (fun _ => (1 : ℂ)) (g * y))) := by
  have hassoc : globalPoints (𝓞 L) L γ * g * y = globalPoints (𝓞 L) L γ * (g * y) := mul_assoc _ _ _
  rw [hassoc]

  have h1 : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 L) L γ * (g * y))) =
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (g * y)) := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  have h2 : NumberField.AdelicHeight.adelicHeight L (globalPoints (𝓞 L) L γ * (g * y)) =
      NumberField.AdelicHeight.adelicHeight L (g * y) :=
    NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero L γ h10 _
  have h3 : NumberField.AdelicHeight.adelicHeight L (adelicWeyl (𝓞 L) L * (globalPoints (𝓞 L) L γ * (g * y))) =
      NumberField.AdelicHeight.adelicHeight L (adelicWeyl (𝓞 L) L * (g * y)) := by
    have : adelicWeyl (𝓞 L) L * (globalPoints (𝓞 L) L γ * (g * y)) =
        globalPoints (𝓞 L) L (gl2Weyl * γ * gl2Weyl⁻¹) * (adelicWeyl (𝓞 L) L * (g * y)) := by
      rw [adelicWeyl, map_mul, map_mul, map_inv]; group
    rw [this]
    exact NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero L _
      (gl2Weyl_conj_apply_one_zero L γ h01) _
  have e1 : Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
        (fun _ => (1 : ℂ)) (globalPoints (𝓞 L) L γ * (g * y)) =
      Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
        (fun _ => (1 : ℂ)) (g * y) := by
    simp only [Set.indicator, Set.mem_setOf_eq, h1]
  have e2 : Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
        (fun _ => (1 : ℂ)) (globalPoints (𝓞 L) L γ * (g * y)) =
      Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
        (fun _ => (1 : ℂ)) (g * y) := by
    simp only [Set.indicator, Set.mem_setOf_eq, h2]
  have e3 : Set.indicator {y' : AdelicGL2 (𝓞 L) L |
          Real.exp R < NumberField.AdelicHeight.adelicHeight L (adelicWeyl (𝓞 L) L * y')}
        (fun _ => (1 : ℂ)) (globalPoints (𝓞 L) L γ * (g * y)) =
      Set.indicator {y' : AdelicGL2 (𝓞 L) L |
          Real.exp R < NumberField.AdelicHeight.adelicHeight L (adelicWeyl (𝓞 L) L * y')}
        (fun _ => (1 : ℂ)) (g * y) := by
    simp only [Set.indicator, Set.mem_setOf_eq, h3]
  rw [e1, e2, e3]

end FDTA9

namespace FDTA9

open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option maxHeartbeats 1600000 in
open scoped TensorProduct.RightActions in
theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Λ₀ : Subgroup (GL (Fin 2) L))
    (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νK)
    (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ) (hθ : Continuous θ) (hθi : Function.Injective θ)
    (hθc : ∀ k : Kˣ, θ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (algebraMap K L : K →* L) k))
    (cH : ℝ) (hcH : 0 < cH)
    (hμH : ∀ f : AdelicGL2 (𝓞 L) L → ENNReal, Measurable f →
      ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂μH =
        ENNReal.ofReal cH * ∫⁻ z, ∫⁻ a, f (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)) ∂νK ∂νZL)
    (e : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ₜ* H)
    (he : ∀ p, ((e p : H) : AdelicGL2 (𝓞 L) L) = AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2))
    (hμ : μH = (ENNReal.ofReal cH) • Measure.map e (νZL.prod νK)) :
    IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H)
      {h : H | ∃ z ∈ ΩL, ∃ a ∈ ΩK,
        (h : AdelicGL2 (𝓞 L) L) = AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)} μH ∧
    ∀ (Ω : Set H), IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH →
      ∀ (y : AdelicGL2 (𝓞 L) L) (R : ℝ),
        (∫⁻ h in Ω, ‖(Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)))‖ₑ ∂μH =
          ENNReal.ofReal cH * ∫⁻ p in ΩL ×ˢ ΩK, ‖(Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)))‖ₑ ∂(νZL.prod νK)) ∧
        (IntegrableOn (fun h : H => (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)))) Ω μH ↔
          IntegrableOn (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ => (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)))) (ΩL ×ˢ ΩK) (νZL.prod νK)) ∧
        ∫ h in Ω, (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y))) ∂μH =
          (cH : ℂ) * ∫ p in ΩL ×ˢ ΩK, (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y))) ∂(νZL.prod νK) := by
  classical

  haveI : SecondCountableTopology (AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ :=
    (NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box K L).1
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ :=
    (NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box K K).1
  haveI : SigmaFinite νZL := by infer_instance
  haveI : SigmaFinite νK := by infer_instance
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace H := Subtype.borelSpace _

  let RL : Subgroup (AdeleRing (𝓞 L) L)ˣ := (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range
  let RK : Subgroup (AdeleRing (𝓞 K) K)ˣ := (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range
  let Γ : Subgroup H := (Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H
  let em : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ᵐ H := e.toHomeomorph.toMeasurableEquiv
  have hem : ∀ p, (em p : H) = e p := fun p => rfl
  have heμ : μH = ENNReal.ofReal cH • Measure.map em (νZL.prod νK) := hμ
  have heΨ : ∀ p, ((e p : H) : AdelicGL2 (𝓞 L) L) = CPMA9.Ψ K L θ p := fun p => (he p).trans (CPMA9.Ψ_apply K L θ p).symm

  have hFD0 : IsFundamentalDomain (↥(RL.prod RK)) (ΩL ×ˢ ΩK) (νZL.prod νK) :=
    isFundamentalDomain_prod RL RK νZL νK hΩL hΩK

  have memΓ : ∀ (q : Lˣ) (k : Kˣ),
      e (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q,
         Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) ∈ Γ := by
    intro q k
    rw [Subgroup.mem_subgroupOf, heΨ, ← globalPoints_lam K L θ hθc q k]
    exact Subgroup.mem_map_of_mem _ (lam_mem K L Λ₀ hΛ₀ q k)
  let toΓ : ↥(RL.prod RK) → ↥Γ := fun δ =>
    ⟨e δ.1, by
      obtain ⟨hq, hk⟩ := Subgroup.mem_prod.mp δ.2
      obtain ⟨q, hq⟩ := hq
      obtain ⟨k, hk⟩ := hk
      have : (δ : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) = (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q,
         Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) := Prod.ext hq.symm hk.symm
      rw [this]
      exact memΓ q k⟩
  have toΓ_coe : ∀ δ, ((toΓ δ : ↥Γ) : H) = e δ.1 := fun δ => rfl
  have toΓ_bij : Function.Bijective toΓ := by
    refine ⟨fun δ δ' h => Subtype.ext (e.injective (congrArg Subtype.val h)), fun γ => ?_⟩
    have hγ : ((γ : H) : AdelicGL2 (𝓞 L) L) ∈ Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L) :=
      Subgroup.mem_subgroupOf.mp γ.2
    obtain ⟨lam0, hlam0, hγeq⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨q, k, rfl⟩ := exists_lam_eq K L Λ₀ hΛ₀ lam0 hlam0
    refine ⟨⟨(Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q,
         Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k),
         Subgroup.mem_prod.mpr ⟨⟨q, rfl⟩, ⟨k, rfl⟩⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [toΓ_coe, heΨ, ← globalPoints_lam K L θ hθc q k, hγeq]
  let eΔΓ : ↥(RL.prod RK) ≃ ↥Γ := Equiv.ofBijective toΓ toΓ_bij
  have hef : ∀ g : ↥Γ, Function.Semiconj (⇑em.toEquiv) (eΔΓ.symm g • ·) (g • ·) := by
    intro g x
    have hg : eΔΓ (eΔΓ.symm g) = g := Equiv.apply_symm_apply _ _
    show em (eΔΓ.symm g • x) = g • em x
    rw [hem, hem, Subgroup.smul_def, Subgroup.smul_def, smul_eq_mul, smul_eq_mul, map_mul]
    congr 1
    conv_rhs => rw [← hg]
    rfl

  have hqmp : Measure.QuasiMeasurePreserving em.symm μH (νZL.prod νK) := by
    refine ⟨em.symm.measurable, ?_⟩
    rw [heμ, Measure.map_smul, MeasurableEquiv.map_symm_map]
    exact Measure.smul_absolutelyContinuous

  have hFDΩ₀ : IsFundamentalDomain (↥Γ) (em '' (ΩL ×ˢ ΩK)) μH :=
    hFD0.image_of_equiv em.toEquiv hqmp eΔΓ.symm hef
  have hΩ₀eq : em '' (ΩL ×ˢ ΩK) = {h : H | ∃ z ∈ ΩL, ∃ a ∈ ΩK,
      (h : AdelicGL2 (𝓞 L) L) = AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)} := by
    ext h
    constructor
    · rintro ⟨⟨z, a⟩, ⟨hz, ha⟩, rfl⟩
      exact ⟨z, hz, a, ha, he (z, a)⟩
    · rintro ⟨z, hz, a, ha, hh⟩
      refine ⟨(z, a), ⟨hz, ha⟩, ?_⟩
      apply Subtype.ext
      rw [hem, he]
      exact hh.symm
  have hFDΩ₀' : IsFundamentalDomain (↥Γ) {h : H | ∃ z ∈ ΩL, ∃ a ∈ ΩK,
      (h : AdelicGL2 (𝓞 L) L) = AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)} μH := by
    rw [← hΩ₀eq]; exact hFDΩ₀
  refine ⟨hFDΩ₀', fun Ω hΩ y R => ?_⟩

  haveI : Countable L := by
    let b := Module.finBasis ℚ L
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := by unfold Matrix; infer_instance
  haveI : Countable (GL (Fin 2) L) :=
    Function.Injective.countable (f := fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L)) fun a b h => Units.ext h
  haveI : Countable ↥(Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)) := by
    have : Function.Surjective (fun l : ↥Λ₀ => (⟨AutomorphicForm.globalPoints (𝓞 L) L l, Subgroup.mem_map_of_mem _ l.2⟩ :
        ↥(Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)))) := by
      rintro ⟨g, hg⟩
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hg
      exact ⟨⟨l, hl⟩, rfl⟩
    exact this.countable
  haveI : Countable ↥Γ :=
    Function.Injective.countable (f := fun γ : ↥Γ => (⟨((γ : H) : AdelicGL2 (𝓞 L) L), Subgroup.mem_subgroupOf.mp γ.2⟩ :
      ↥(Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)))) fun γ γ' h => by
        have h' := congrArg Subtype.val h
        simp only at h'
        exact Subtype.ext (Subtype.ext h')
  haveI : MeasurableConstSMul (↥Γ) (↥H) := ⟨fun γ => by
    show Measurable fun h : H => (γ : H) * h
    exact measurable_const_mul _⟩
  haveI : SMulInvariantMeasure (↥Γ) (↥H) μH := ⟨fun γ s hs => by
    show μH ((fun h : H => (γ : H) * h) ⁻¹' s) = μH s
    exact measure_preimage_mul μH (γ : H) s⟩

  set T : AdelicGL2 (𝓞 L) L → ℂ := fun g =>
    Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
        (fun _ => (1 : ℂ)) g *
      ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
          (fun _ => (1 : ℂ)) g
        - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
            Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
          (fun _ => (1 : ℂ)) g) with hT
  have hinv : ∀ (γ : ↥Γ) (h : H), T (((γ • h : H) : AdelicGL2 (𝓞 L) L) * y) = T ((h : AdelicGL2 (𝓞 L) L) * y) := by
    intro γ h
    have hγ : ((γ : H) : AdelicGL2 (𝓞 L) L) ∈ Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L) :=
      Subgroup.mem_subgroupOf.mp γ.2
    obtain ⟨lam0, hlam0, hγeq⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨h10, h01, -⟩ := (hΛ₀ lam0).mp hlam0
    have : ((γ • h : H) : AdelicGL2 (𝓞 L) L) = AutomorphicForm.globalPoints (𝓞 L) L lam0 * (h : AdelicGL2 (𝓞 L) L) := by
      rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, hγeq]
    rw [this, hT]
    exact integrand_invariant L α β y R lam0 h10 h01 (h : AdelicGL2 (𝓞 L) L)
  have hinv' : ∀ (γ : ↥Γ) (h : H),
      (fun h : H => T ((h : AdelicGL2 (𝓞 L) L) * y)) (γ • h) = (fun h : H => T ((h : AdelicGL2 (𝓞 L) L) * y)) h :=
    hinv
  have hinvE : ∀ (γ : ↥Γ) (h : H),
      (fun h : H => ‖T ((h : AdelicGL2 (𝓞 L) L) * y)‖ₑ) (γ • h) = (fun h : H => ‖T ((h : AdelicGL2 (𝓞 L) L) * y)‖ₑ) h := by
    intro γ h; simp only [hinv]
  refine ⟨?_, ?_, ?_⟩
  ·
    have h1 := hΩ.setLIntegral_eq hFDΩ₀' (fun h : H => ‖T ((h : AdelicGL2 (𝓞 L) L) * y)‖ₑ) hinvE
    rw [← hΩ₀eq, setLIntegral_eq em (νZL.prod νK) μH cH heμ] at h1
    simp only [hT, hem, he] at h1
    exact h1
  ·
    have h1 := hΩ.integrableOn_iff hFDΩ₀' (f := fun h : H => T ((h : AdelicGL2 (𝓞 L) L) * y)) hinv'
    rw [← hΩ₀eq, integrableOn_iff em (νZL.prod νK) μH cH hcH heμ] at h1
    simp only [hT, hem, he] at h1
    exact h1
  ·
    have h1 := hΩ.setIntegral_eq hFDΩ₀' (f := fun h : H => T ((h : AdelicGL2 (𝓞 L) L) * y)) hinv'
    rw [← hΩ₀eq, setIntegral_eq em (νZL.prod νK) μH cH hcH heμ] at h1
    simp only [hT, hem, he] at h1
    exact h1

end FDTA9

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

private theorem _root_.FDT.integrableOn_iff (S : Set H) (g : H → ℂ) :
    IntegrableOn g S μH ↔ IntegrableOn (fun p => g (e p)) (e ⁻¹' S) (νZL.prod νK) := by
  obtain ⟨em, hem⟩ := exists_measurableEquiv K L H e
  rw [hμ, IntegrableOn, Measure.restrict_smul,
    integrable_smul_measure (ofReal_cH_ne_zero cH hcH) ENNReal.ofReal_ne_top, ← hem]
  exact integrableOn_map_equiv em

p2m_export "FDT" "integrableOn_iff"
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

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Λ₀ : Subgroup (GL (Fin 2) L))
    (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νK)
    (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ) (hθ : Continuous θ) (hθi : Function.Injective θ)
    (hθc : ∀ k : Kˣ, θ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (algebraMap K L : K →* L) k))
    (cH : ℝ) (hcH : 0 < cH)
    (hμH : ∀ f : AdelicGL2 (𝓞 L) L → ENNReal, Measurable f →
      ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂μH =
        ENNReal.ofReal cH * ∫⁻ z, ∫⁻ a, f (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)) ∂νK ∂νZL) :
    IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H)
      {h : H | ∃ z ∈ ΩL, ∃ a ∈ ΩK,
        (h : AdelicGL2 (𝓞 L) L) = AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)} μH ∧
    ∀ (Ω : Set H), IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH →
      ∀ (y : AdelicGL2 (𝓞 L) L) (R : ℝ),
        (∫⁻ h in Ω, ‖(Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)))‖ₑ ∂μH =
          ENNReal.ofReal cH * ∫⁻ p in ΩL ×ˢ ΩK, ‖(Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)))‖ₑ ∂(νZL.prod νK)) ∧
        (IntegrableOn (fun h : H => (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)))) Ω μH ↔
          IntegrableOn (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ => (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)))) (ΩL ×ˢ ΩK) (νZL.prod νK)) ∧
        ∫ h in Ω, (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y))) ∂μH =
          (cH : ℂ) * ∫ p in ΩL ×ˢ ΩK, (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y))) ∂(νZL.prod νK) := by
  obtain ⟨e, he, hμ⟩ := FDT.exists_equiv K L H hHc μH νZL νK θ hθ hθi cH hcH hμH
  exact FDTA9.main K L α β νZL ΩL hΩL D σ hgen H hHc hH μH Λ₀ hΛ₀ νK ΩK hΩK θ hθ hθi hθc cH hcH hμH e
    (fun p => (he p).trans (CPMA9.Ψ_apply K L θ p)) hμ

end S_AutomorphicForm_isFundamentalDomain_image_and_forall_setLIntegral_torusShell_eq_mul_setLIntegral_prod
end P2MW
export P2MW.S_AutomorphicForm_isFundamentalDomain_image_and_forall_setLIntegral_torusShell_eq_mul_setLIntegral_prod (solution)
