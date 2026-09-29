-- Prove2me | solution 1 for AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ca42f1e2-f446-5220-9250-54075dc0873a

import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_orbital_add_sum_weightedOrbital_or_eq_zero_of_isFactorizableTestFn
import Theorems.Thm_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bare
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply"
p2m_attr_erase "simp" "Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace R4AGlue

theorem assemble_logic {Φ Ψ ι : Type*} [Nonempty Φ]
    {fact : (ι → ℕ) → (ι → ℕ) → Φ → Ψ → Prop} {good : Φ → Prop} {body : Φ → ℝ → ℂ → ℂ → Prop}
    (huniq : ∀ (ks js : ι → ℕ) (φ₁ : Φ) (ψ₁ : Ψ) (φ₂ : Φ) (ψ₂ : Ψ),
      fact ks js φ₁ ψ₁ → fact ks js φ₂ ψ₂ → φ₁ = φ₂)
    (hgood : ∀ (ks js : ι → ℕ) (φ : Φ) (ψ : Ψ), fact ks js φ ψ → good φ)
    (key : ∀ φ : Φ, good φ → ∃ (ν μ : ℂ) (R₀ : ℝ), ∀ R : ℝ, R₀ ≤ R → body φ R ν μ) :
    ∃ μ ν : (ι → ℕ) → (ι → ℕ) → ℂ, ∀ (ks js : ι → ℕ) (φ : Φ) (ψ : Ψ), fact ks js φ ψ →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → body φ R (ν ks js) (μ ks js) := by
  classical

  have key' : ∀ φ : Φ, ∃ c : ℂ × ℂ, good φ → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → body φ R c.1 c.2 := by
    intro φ
    by_cases hφ : good φ
    · obtain ⟨ν, μ, R₀, h⟩ := key φ hφ
      exact ⟨(ν, μ), fun _ => ⟨R₀, h⟩⟩
    · exact ⟨(0, 0), fun h => (hφ h).elim⟩
  choose coef hcoef using key'

  have sel : ∀ ks js : ι → ℕ, ∃ φ₀ : Φ, ∀ (φ : Φ) (ψ : Ψ), fact ks js φ ψ → φ = φ₀ := by
    intro ks js
    by_cases h : ∃ (φ : Φ) (ψ : Ψ), fact ks js φ ψ
    · obtain ⟨φ₀, ψ₀, h₀⟩ := h
      exact ⟨φ₀, fun φ ψ hφ => huniq ks js φ ψ φ₀ ψ₀ hφ h₀⟩
    · exact ⟨Classical.arbitrary Φ, fun φ ψ hφ => (h ⟨φ, ψ, hφ⟩).elim⟩
  choose phi0 hphi0 using sel
  refine ⟨fun ks js => (coef (phi0 ks js)).2, fun ks js => (coef (phi0 ks js)).1, ?_⟩
  intro ks js φ ψ hf
  obtain rfl := hphi0 ks js φ ψ hf
  exact hcoef _ (hgood ks js _ ψ hf)

section TwistCentral

variable {G : Type*} [Group G]

def twistCentralSubgroup (f : G →* G) : Subgroup G where
  carrier := {h | f h * h⁻¹ ∈ Subgroup.center G}
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one, inv_one, mul_one]
    exact Subgroup.one_mem _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have hc := Subgroup.mem_center_iff.mp hb
    have : f (a * b) * (a * b)⁻¹ = (f a * a⁻¹) * (a * (f b * b⁻¹) * a⁻¹) := by
      simp only [map_mul, mul_inv_rev]; group
    rw [this, hc a, mul_inv_cancel_right]
    exact Subgroup.mul_mem _ ha hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hc := Subgroup.mem_center_iff.mp ha
    have : f a⁻¹ * a⁻¹⁻¹ = (a⁻¹ * (f a * a⁻¹) * a)⁻¹ := by
      simp only [map_inv]; group
    rw [this, hc a⁻¹, inv_mul_cancel_right]
    exact Subgroup.inv_mem _ ha

theorem mem_twistCentralSubgroup (f : G →* G) (h : G) :
    h ∈ twistCentralSubgroup f ↔ f h * h⁻¹ ∈ Subgroup.center G := Iff.rfl

end TwistCentral

section Diag

variable (A : Type*) [CommRing A]

def diagSubgroup : Subgroup (GL (Fin 2) A) where
  carrier := {h | (h : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 ∧ (h : Matrix (Fin 2) (Fin 2) A) 0 1 = 0}
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> simp
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha1, ha2, hb1, hb2]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩ <;>
      simp [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, ha1, ha2]

variable {A}

theorem mem_diagSubgroup (h : GL (Fin 2) A) :
    h ∈ diagSubgroup A ↔
      (h : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 ∧ (h : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := Iff.rfl

theorem mul_comm_of_mem_diagSubgroup {a b : GL (Fin 2) A} (ha : a ∈ diagSubgroup A)
    (hb : b ∈ diagSubgroup A) : a * b = b * a := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine Units.ext ?_
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [ha1, ha2, hb1, hb2, mul_comm]

end Diag

section H

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

def theH : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  diagSubgroup (AdeleRing (𝓞 L) L) ⊓ twistCentralSubgroup (AutomorphicForm.sigmaAdelicAct K L D σ)

theorem mem_theH (h : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    h ∈ theH K L D σ ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈
         Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)) := by
  rw [theH, Subgroup.mem_inf, mem_diagSubgroup, mem_twistCentralSubgroup, and_assoc]

theorem isClosed_theH :
    IsClosed ((theH K L D σ : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L)) :
      Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) := by
  have h1 : IsClosed {h : AutomorphicForm.AdelicGL2 (𝓞 L) L |
      (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0} :=
    isClosed_eq (Units.continuous_val.matrix_elem 1 0) continuous_const
  have h2 : IsClosed {h : AutomorphicForm.AdelicGL2 (𝓞 L) L |
      (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0} :=
    isClosed_eq (Units.continuous_val.matrix_elem 0 1) continuous_const
  have hZ : IsClosed ((Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L)) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) := by
    have : ((Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L)) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) =
        ⋂ g : AutomorphicForm.AdelicGL2 (𝓞 L) L, {z | g * z = z * g} := by
      ext z
      simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun g =>
      isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  have h3 : IsClosed {h : AutomorphicForm.AdelicGL2 (𝓞 L) L |
      AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈
        Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)} :=
    hZ.preimage ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).mul continuous_inv)
  have hEq : ((theH K L D σ : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L)) :
      Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) =
      ({h : AutomorphicForm.AdelicGL2 (𝓞 L) L |
          (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0} ∩
        {h : AutomorphicForm.AdelicGL2 (𝓞 L) L |
          (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0}) ∩
      {h : AutomorphicForm.AdelicGL2 (𝓞 L) L |
        AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈
          Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)} := by
    ext h
    simp only [SetLike.mem_coe, mem_theH, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
  rw [hEq]
  exact (h1.inter h2).inter h3

theorem theH_mul_comm (a b : theH K L D σ) : a * b = b * a := by
  refine Subtype.ext ?_
  show (a : AutomorphicForm.AdelicGL2 (𝓞 L) L) * b = b * a
  exact mul_comm_of_mem_diagSubgroup (Subgroup.mem_inf.mp a.2).1 (Subgroup.mem_inf.mp b.2).1

theorem exists_haar_theH :
    ∃ μH : Measure (theH K L D σ), μH.IsHaarMeasure ∧ μH.IsMulRightInvariant := by
  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : LocallyCompactSpace (theH K L D σ) := (isClosed_theH K L D σ).locallyCompactSpace
  refine ⟨Measure.haar, inferInstance, ⟨fun g => ?_⟩⟩
  have : (fun x : theH K L D σ => x * g) = fun x => g * x := funext fun x => theH_mul_comm K L D σ x g
  rw [this]
  exact map_mul_left_eq_self _ g

end H

section Delta

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

include hgen in

theorem exists_Delta : ∃ Δ : Set (GL (Fin 2) L),
    (∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1) ∧
    (∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) ∧
    ({δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} ⊆
      ⋃ t ∈ Δ, {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) := by
  classical
  obtain ⟨-, h2, h3⟩ :=
    LT.TwistedNorm.setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal (K := K) (L := L) hgen

  let cls : GL (Fin 2) L → Set (GL (Fin 2) L) := fun t => {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
    t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
  let good : GL (Fin 2) L → Prop := fun t =>
    ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1

  let S : Set (Set (GL (Fin 2) L)) := {s | ∃ t, good t ∧ cls t = s}
  have hS : ∀ s : S, ∃ t, good t ∧ cls t = s := fun s => s.2
  choose pick hpick using hS
  refine ⟨Set.range pick, ?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(hpick s).1.1.1, (hpick s).1.1.2, (hpick s).1.2⟩
  · rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩ hne
    have hss : (s : Set (GL (Fin 2) L)) ≠ s' := fun h => hne (by rw [Subtype.ext h])
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne'
    have h := ((h3 (pick s') (pick s) (hpick s').1.1 (hpick s).1.1).1).mp hne'
    exact hss (by rw [← (hpick s).2, ← (hpick s').2]; exact h)
  · intro δ hδ
    obtain ⟨t, htd, htN, ht⟩ := h2 δ hδ
    have hs : cls t ∈ S := ⟨t, ⟨htd, htN⟩, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨pick ⟨_, hs⟩, ⟨⟨_, hs⟩, rfl⟩, ?_⟩
    have hct : cls (pick ⟨cls t, hs⟩) = cls t := (hpick ⟨_, hs⟩).2
    show δ ∈ cls (pick ⟨cls t, hs⟩)
    rw [hct]
    exact ht

end Delta

section Fact

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open scoped TensorProduct.RightActions in

theorem eq_of_isSemiLocalFactorization (S : Finset (HeightOneSpectrum (𝓞 K)))
    {φ₁ φ₂ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ}
    {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ}
    {φf₁ φf₂ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    {φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (h₁ : AutomorphicForm.IsSemiLocalFactorization K L S φ₁ φa φf₁ φS)
    (h₂ : AutomorphicForm.IsSemiLocalFactorization K L S φ₂ φa φf₂ φS) : φ₁ = φ₂ := by
  obtain ⟨-, -, -, hint₁, hout₁, hφ₁⟩ := h₁
  obtain ⟨-, -, -, hint₂, hout₂, hφ₂⟩ := h₂
  have hf : φf₁ = φf₂ := by
    funext h
    by_cases hh : ∀ v ∉ S,
        AutomorphicForm.semiLocalComponent K L v h ∈ AutomorphicForm.semiLocalIntegralSet K L v
    · rw [hint₁ h hh, hint₂ h hh]
    · push Not at hh
      rw [hout₁ h hh, hout₂ h hh]
  funext g
  rw [hφ₁ g, hφ₂ g, hf]

open scoped TensorProduct.RightActions in

theorem continuous_and_hasCompactSupport_of_isSemiLocalFactorization
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ}
    {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ}
    {φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    {φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (h : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS) :
    Continuous φ ∧ HasCompactSupport φ :=
  AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ
    ⟨φa, φf, h.1, h.2.1, h.2.2.2.2.2⟩

end Fact

end R4AGlue

namespace R4AGlue

open AutomorphicForm

def Body (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ) (ν μ : ℂ) : Prop :=
  (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      (R : ℂ) * ν + μ

theorem perPhi
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : AutomorphicForm.IsFactorizableTestFn L φ) :
    ∃ (ν μ : ℂ) (R₀ : ℝ), ∀ R : ℝ, R₀ ≤ R → Body K L ΦL νZL ΩL D σ hgen ξL Φ₀ φ R ν μ := by

  obtain ⟨μH, hμH, hμHr⟩ := exists_haar_theH K L D σ

  obtain ⟨Δ, hΔd, hΔdisj, hΔcov⟩ := exists_Delta (K := K) (L := L) (σ := σ) hgen

  have hE :=
    AutomorphicForm.exists_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_orbital_add_sum_weightedOrbital_or_eq_zero_of_isFactorizableTestFn
      K L α β hα hαβ ΦL νZL ΩL hΩL D σ hgen ξL hξc hξt c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀
      (theH K L D σ) (isClosed_theH K L D σ) (mem_theH K L D σ) μH Δ hΔd hΔdisj hΔcov
  by_cases hinv : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩
  ·
    obtain ⟨a, -, hA⟩ := hE.1 hinv
    obtain ⟨Δφ, -, -, -, R₀, hR₀⟩ := hA φ hφ
    exact ⟨_, _, R₀, fun R hR => hR₀ R hR⟩
  ·
    obtain ⟨R₀, hR₀⟩ := hE.2 hinv φ hφ
    refine ⟨0, 0, R₀, fun R hR => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hR₀ R hR
    refine ⟨h1, h2, ?_⟩
    rw [h3]
    ring

end R4AGlue

end

open AutomorphicForm in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
      ∃ μ ν : (HeightOneSpectrum (𝓞 K) → ℕ) → (HeightOneSpectrum (𝓞 K) → ℕ) → ℂ,
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      (R : ℂ) * ν ks js + μ ks js := by
  intro T hT hTS ws w' hw' ϖs hϖ hϖs0 ns rTs hrTs zs hzs
  exact R4AGlue.assemble_logic
    (fact := fun (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ) =>
      IsSemiLocalFactorization K L (S ∪ T) φ φa φf
        (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
          ∑ ι : Fin (ks v) → Fin (ns v),
            (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
              ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
          else φS v))
    (good := fun φ : AdelicGL2 (𝓞 L) L → ℂ => AutomorphicForm.IsFactorizableTestFn L φ)
    (body := R4AGlue.Body K L ΦL νZL ΩL D σ hgen ξL Φ₀)
    (fun ks js φ₁ ψ₁ φ₂ ψ₂ h₁ h₂ => R4AGlue.eq_of_isSemiLocalFactorization K L (S ∪ T) h₁ h₂)
    (fun ks js φ ψ h => (⟨φa, ψ, h.1, h.2.1, h.2.2.2.2.2⟩ : AutomorphicForm.IsFactorizableTestFn L φ))
    (fun φ hφ => R4AGlue.perPhi K L α β hα hαβ ΦL νZL ΩL hΩL D σ hgen ξL hξc hξt c u d₁ d₂ hc Tc hTc
      Φ₀ hΦ₀S hΦ₀s hΦ₀ φ hφ)

end S_AutomorphicForm_forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bare
end P2MW
export P2MW.S_AutomorphicForm_forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bare (solution)
