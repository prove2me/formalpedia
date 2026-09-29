-- Prove2me | solution 1 for AutomorphicForm.hasSum_setIntegral_setIntegral_twistedOrbital_of_normClass_elliptic_or_central
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f9cc23af-e32e-59f5-9f61-32466d353dad

import Theorems.Thm_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasSum_setIntegral_setIntegral_twistedOrbital_of_normClass_elliptic_or_central
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar Filter Function Set
open scoped ENNReal Topology

noncomputable section

namespace R3TwFold

section Instances

variable (L : Type) [Field L] [NumberField L]

theorem secondCountableTopology_adeleRing : SecondCountableTopology (AdeleRing (𝓞 L) L) :=
  NumberField.AdeleRing.secondCountableTopology L

theorem secondCountableTopology_mulOpposite {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology

theorem secondCountableTopology_units {M : Type*} [TopologicalSpace M] [Monoid M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ := secondCountableTopology_mulOpposite
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem secondCountableTopology_ideles : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := secondCountableTopology_adeleRing L
  exact secondCountableTopology_units

theorem secondCountableTopology_adelicGL2 :
    SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := secondCountableTopology_adeleRing L
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 L) L))
  exact secondCountableTopology_units

end Instances

section Algebra

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem sigmaAdelicAct_centralScalar (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) =
      AutomorphicForm.centralScalar (𝓞 L) L
        (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [AutomorphicForm.sigmaAdelicAct, AutomorphicForm.centralScalar,
    Matrix.GeneralLinearGroup.map_apply]
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom)
      (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) (((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L w * y = y * AutomorphicForm.centralScalar (𝓞 L) L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j

theorem twist_centralScalar_mul (σ : L ≃ₐ[K] L) (g x : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    x⁻¹ * g * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x) =
      x⁻¹ * g * AutomorphicForm.sigmaAdelicAct K L D σ x *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) := by
  rw [map_mul, sigmaAdelicAct_centralScalar, centralScalar_comm]
  simp only [mul_assoc]

theorem continuous_centralScalar :
    Continuous (AutomorphicForm.centralScalar (𝓞 L) L :
      (AdeleRing (𝓞 L) L)ˣ → AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  have hsc : Continuous (Matrix.scalar (Fin 2) : AdeleRing (𝓞 L) L → Matrix (Fin 2) (Fin 2) _) := by
    refine continuous_matrix fun i j => ?_
    by_cases hij : i = j
    · subst hij; (simp [Matrix.scalar_apply]; exact continuous_id)
    · simpa [Matrix.scalar_apply, hij] using continuous_const
  exact Continuous.units_map _ hsc

end Algebra

section Slab

variable (L : Type) [Field L] [NumberField L]

def slab (α β : ℝ) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem ideleNorm_det_globalPoints (γ : GL (Fin 2) L) :
    NumberField.TateGlobal.ideleNorm L
      (Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 L) L γ)) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  unfold NumberField.TateGlobal.ideleNorm AutomorphicForm.globalPoints
  rw [Matrix.GeneralLinearGroup.map_det]
  have := NumberField.AdeleRing.distribHaarChar_algebraMap L (Matrix.GeneralLinearGroup.det γ)
  simp only [RingHom.toMonoidHom_eq_coe] at this
  rw [this]
  simp

theorem globalPoints_mul_mem_slab_iff (α β : ℝ) (γ : GL (Fin 2) L)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.globalPoints (𝓞 L) L γ * g ∈ slab L α β ↔ g ∈ slab L α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    ideleNorm_det_globalPoints, one_mul]

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem borelSpace_adelicGL2 : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L

attribute [local instance] borelSpace_adelicGL2

theorem smulInvariantMeasure_restrict_slab (α β : ℝ) :
    SMulInvariantMeasure (AutomorphicForm.globalPoints (𝓞 L) L).range
      (AutomorphicForm.AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  refine ⟨fun γ s hs => ?_⟩
  obtain ⟨_, γ, rfl⟩ := γ
  have hmeas : MeasurableSet ((fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      AutomorphicForm.globalPoints (𝓞 L) L γ * x) ⁻¹' s) := (measurable_const_mul _) hs
  change ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β))
      ((fun x => AutomorphicForm.globalPoints (𝓞 L) L γ * x) ⁻¹' s) = _
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => AutomorphicForm.globalPoints (𝓞 L) L γ * x) ⁻¹' s ∩ slab L α β =
      (fun x => AutomorphicForm.globalPoints (𝓞 L) L γ * x) ⁻¹' (s ∩ slab L α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, globalPoints_mul_mem_slab_iff]
  rw [hset, measure_preimage_mul]

end Slab

section LocalFiniteness

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem globalPoints_eq_of_eq (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ)
    (δ : GL (Fin 2) L) :
    AutomorphicForm.globalPoints (𝓞 L) L δ =
      x * (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) *
        (AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))⁻¹ := by
  group

theorem finite_setOf_exists_apply_ne_zero {N : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ)}
    (hN : IsCompact N) {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ} (hφc : HasCompactSupport φ) :
    {δ : GL (Fin 2) L | ∃ p ∈ N, φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1)) ≠ 0}.Finite := by

  set F : (AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AutomorphicForm.AdelicGL2 (𝓞 L) L →
      AutomorphicForm.AdelicGL2 (𝓞 L) L := fun q =>
    q.1.1 * q.2 * (AutomorphicForm.sigmaAdelicAct K L D σ
      (AutomorphicForm.centralScalar (𝓞 L) L q.1.2 * q.1.1))⁻¹ with hF
  have hFc : Continuous F := by
    have h1 : Continuous fun q : (AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) ×
        AutomorphicForm.AdelicGL2 (𝓞 L) L => q.1.1 := continuous_fst.comp continuous_fst
    have h2 : Continuous fun q : (AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) ×
        AutomorphicForm.AdelicGL2 (𝓞 L) L => q.1.2 := continuous_snd.comp continuous_fst
    have h3 : Continuous fun q : (AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) ×
        AutomorphicForm.AdelicGL2 (𝓞 L) L =>
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L q.1.2 * q.1.1) :=
      (AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp
        (((continuous_centralScalar L).comp h2).mul h1)
    exact ((h1.mul continuous_snd).mul h3.inv)
  have hC : IsCompact (F '' (N ×ˢ tsupport φ)) := (hN.prod hφc).image hFc
  have hfin := AutomorphicForm.adelicKernelLocalFiniteness L _ hC 1 1
  refine hfin.subset fun δ hδ => ?_
  obtain ⟨p, hp, hne⟩ := hδ
  simp only [Set.mem_setOf_eq, inv_one, one_mul, mul_one]
  refine ⟨⟨p, _⟩, ⟨hp, subset_tsupport _ (Function.mem_support.2 hne)⟩, ?_⟩
  simp only [hF]
  exact (globalPoints_eq_of_eq K L D σ p.1 p.2 δ).symm

end LocalFiniteness

section ClassSums

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem countable_GL2 : Countable (GL (Fin 2) L) := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

def hfun (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)
    (δ : GL (Fin 2) L) (p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  ((ξ ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) *
    φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1))

theorem continuous_twistArg (δ : GL (Fin 2) L) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1) :=
  ((continuous_fst.inv).mul continuous_const).mul
    ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp
      (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst))

theorem continuous_hfun {ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ}
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (δ : GL (Fin 2) L) :
    Continuous (hfun K L D σ ξ φ δ) :=
  (hξc.comp continuous_snd).mul (hφ.comp (continuous_twistArg K L D σ δ))

theorem exists_finset_tsum_eq_sum {ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ}
    {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ} (hφc : HasCompactSupport φ) (P : GL (Fin 2) L → Prop)
    {N : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ)} (hN : IsCompact N) :
    ∃ S : Finset {δ : GL (Fin 2) L // P δ}, ∀ p ∈ N,
      (∀ δ : {δ : GL (Fin 2) L // P δ}, δ ∉ S → hfun K L D σ ξ φ δ p = 0) ∧
      ∑' δ : {δ : GL (Fin 2) L // P δ}, hfun K L D σ ξ φ δ p =
        ∑ δ ∈ S, hfun K L D σ ξ φ δ p := by
  have hfin := finite_setOf_exists_apply_ne_zero K L D σ hN hφc
  have hfin' : (Subtype.val ⁻¹' {δ : GL (Fin 2) L | ∃ p ∈ N, φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1)) ≠ 0} :
      Set {δ : GL (Fin 2) L // P δ}).Finite := hfin.preimage Subtype.val_injective.injOn
  refine ⟨hfin'.toFinset, fun p hp => ?_⟩
  have hzero : ∀ δ : {δ : GL (Fin 2) L // P δ}, δ ∉ hfin'.toFinset → hfun K L D σ ξ φ δ p = 0 := by
    intro δ hδ
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq, not_exists] at hδ
    have := hδ p
    rw [not_and, not_not] at this
    simp only [hfun, this hp, mul_zero]
  refine ⟨hzero, tsum_eq_sum' ?_⟩
  intro δ hδ
  by_contra h
  exact hδ (hzero δ h)

theorem continuous_tsum_hfun {ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ}
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (P : GL (Fin 2) L → Prop) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∑' δ : {δ : GL (Fin 2) L // P δ}, hfun K L D σ ξ φ δ p := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨N, hN, hNp⟩ := exists_compact_mem_nhds p₀
  obtain ⟨S, hS⟩ := exists_finset_tsum_eq_sum K L D σ hφc P hN
  have hcont : Continuous fun p => ∑ δ ∈ S, hfun K L D σ ξ φ δ p :=
    continuous_finsetSum S fun δ _ => continuous_hfun K L D σ hξc hφ δ
  have hon : ContinuousOn (fun p => ∑' δ : {δ : GL (Fin 2) L // P δ}, hfun K L D σ ξ φ δ p) N :=
    hcont.continuousOn.congr fun p hp => (hS p hp).2
  exact hon.continuousAt hNp

theorem tsum_hfun_eq_mul_finsum {ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ}
    {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ} (hφc : HasCompactSupport φ) (P : GL (Fin 2) L → Prop)
    (p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) :
    ∑' δ : {δ : GL (Fin 2) L // P δ}, hfun K L D σ ξ φ δ p =
      ((ξ ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) *
        ∑ᶠ δ ∈ {δ : GL (Fin 2) L | P δ}, φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1)) := by
  have hfin := finite_setOf_exists_apply_ne_zero K L D σ (isCompact_singleton (x := p)) hφc
  set g : GL (Fin 2) L → ℂ := fun δ => φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1)) with hg
  have hsupp : (Function.support fun δ : {δ : GL (Fin 2) L // P δ} => g δ).Finite := by
    refine (hfin.preimage Subtype.val_injective.injOn).subset fun δ hδ => ?_
    exact ⟨p, Set.mem_singleton p, hδ⟩
  have h1 : ∑' δ : {δ : GL (Fin 2) L // P δ}, hfun K L D σ ξ φ δ p =
      ((ξ ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) * ∑' δ : {δ : GL (Fin 2) L // P δ}, g δ := by
    rw [← tsum_mul_left]; rfl
  rw [h1, tsum_eq_finsum hsupp]
  congr 1
  exact finsum_set_coe_eq_finsum_mem (s := {δ | P δ}) (f := g)

end ClassSums

section Main

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] borelSpace_adelicGL2

theorem main
    (σ : L ≃ₐ[K] L) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (α β : ℝ) (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆ slab L α β)
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZ : Measure (AdeleRing (𝓞 L) L)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
(ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (rep : LT.TwistedNorm.SigmaConjClasses σ → GL (Fin 2) L)
    (hrep : ∀ c, LT.TwistedNorm.SigmaConjClasses.mk σ (rep c) = c)
    (Ψ : LT.TwistedNorm.SigmaConjClasses σ → Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (Q : LT.TwistedNorm.SigmaConjClasses σ → Prop)
    (hΨ : ∀ c, Q c → IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (rep c)).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) (Ψ c)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (habs : ∫⁻ x in Φ, ∫⁻ z in Ω,
        ∑' δ : {δ : GL (Fin 2) L // Q (LT.TwistedNorm.SigmaConjClasses.mk σ δ)},
          ‖hfun K L D σ ξ φ δ (x, z)‖ₑ ∂νZ ∂(adelicGLHaar (Fin 2) (𝓞 L) L) < ⊤) :
    HasSum
      (fun c : {c : LT.TwistedNorm.SigmaConjClasses σ // Q c} =>
        ∫ x in Ψ c, (∫ z in Ω, hfun K L D σ ξ φ (rep c) (x, z) ∂νZ)
          ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
      (∫ x in Φ, (∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∑ᶠ δ ∈ {δ : GL (Fin 2) L | Q (LT.TwistedNorm.SigmaConjClasses.mk σ δ)},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZ)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) := by

  haveI hSCG : SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) := secondCountableTopology_adelicGL2 L
  haveI hSCZ : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_ideles L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI : SigmaCompactSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) := inferInstance
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := inferInstance
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 L) L) := inferInstance
  haveI : SigmaFinite νZ := inferInstance
  haveI := smulInvariantMeasure_restrict_slab L α β
  haveI : Countable (GL (Fin 2) L) := countable_GL2 L
  haveI : Countable (LT.TwistedNorm.SigmaConjClasses σ) :=
    (LT.TwistedNorm.SigmaConjClasses.mk_surjective σ).countable

  set Haar := adelicGLHaar (Fin 2) (𝓞 L) L with hHaar
  set μ : Measure (AutomorphicForm.AdelicGL2 (𝓞 L) L) := Haar.restrict (slab L α β) with hμ
  set σA := AutomorphicForm.sigmaAdelicAct K L D σ with hσA
  set I := {δ : GL (Fin 2) L // Q (LT.TwistedNorm.SigmaConjClasses.mk σ δ)} with hI
  set CC := {c : LT.TwistedNorm.SigmaConjClasses σ // Q c} with hCC
  set h : GL (Fin 2) L → AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ → ℂ :=
    hfun K L D σ ξ φ with hh
  have hμΦ : μ.restrict Φ = Haar.restrict Φ := Measure.restrict_restrict_of_subset hΦs

  set Fz : (AdeleRing (𝓞 L) L)ˣ → AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ := fun z y =>
    ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (y * σA (AutomorphicForm.centralScalar (𝓞 L) L z)) with hFz
  have hFz_eq : ∀ (z : (AdeleRing (𝓞 L) L)ˣ) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (δ : GL (Fin 2) L),
      Fz z (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * σA x) = h δ (x, z) := by
    intro z x δ
    simp only [hFz, hh, hfun, hσA, twist_centralScalar_mul]
  have hFz_sm : ∀ z, StronglyMeasurable (Fz z) := fun z =>
    (continuous_const.mul (hφ.comp (continuous_id.mul continuous_const))).stronglyMeasurable

  have hcont : ∀ δ, Continuous (h δ) := fun δ => continuous_hfun K L D σ hξc hφ δ
  have hGm : Measurable fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∑' δ : I, ‖h δ p‖ₑ :=
    Measurable.tsum fun δ => (hcont δ).measurable.enorm

  set T : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞ := fun z => ∫⁻ x in Φ, ∑' δ : I, ‖h δ (x, z)‖ₑ ∂Haar with hT
  have hTm : Measurable T := hGm.lintegral_prod_left'
  have hswap : ∫⁻ z in Ω, T z ∂νZ = ∫⁻ x in Φ, ∫⁻ z in Ω, ∑' δ : I, ‖h δ (x, z)‖ₑ ∂νZ ∂Haar := by
    simp only [hT]
    exact (lintegral_lintegral_swap (μ := Haar.restrict Φ) (ν := νZ.restrict Ω)
      (f := fun x z => ∑' δ : I, ‖h δ (x, z)‖ₑ) hGm.aemeasurable).symm
  have hTfin : ∫⁻ z in Ω, T z ∂νZ < ⊤ := by rw [hswap]; exact habs
  have hae : ∀ᵐ z ∂νZ.restrict Ω, T z < ⊤ := ae_lt_top hTm hTfin.ne

  have hrep' : ∀ c ∈ {c | Q c}, LT.TwistedNorm.SigmaConjClasses.mk σ (rep c) = c := fun c _ => hrep c
  have hΨ' : ∀ c ∈ {c | Q c}, IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (rep c)).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) (Ψ c) μ := fun c hc => hΨ c hc
  have G1 : ∀ z, T z < ⊤ →
      (∑' c : CC, ∫⁻ x in Ψ c, ‖h (rep c) (x, z)‖ₑ ∂μ = T z) ∧
      (∀ c : CC, IntegrableOn (fun x => h (rep c) (x, z)) (Ψ c) μ) ∧
      HasSum (fun c : CC => ∫ x in Ψ c, h (rep c) (x, z) ∂μ) (∫ x in Φ, ∑' δ : I, h δ (x, z) ∂Haar) := by
    intro z hz
    have habsz : ∫⁻ x in Φ, ∑' δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ {c | Q c}},
        ‖Fz z (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * σA x)‖ₑ ∂μ < ⊤ := by
      simp_rw [hFz_eq]
      rw [hμΦ]
      exact hz
    have key := AutomorphicForm.hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top K L (𝓞 L)
      σ σA (AutomorphicForm.continuous_sigmaAdelicAct K L D σ)
      (fun γ => AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ γ) μ Φ hΦ {c | Q c} rep hrep' Ψ hΨ'
      (Fz z) (hFz_sm z) habsz
    simp_rw [hFz_eq] at key
    rw [hμΦ] at key
    exact ⟨key.1, fun c => key.2.1 c c.2, key.2.2⟩

  set Gc : CC → (AdeleRing (𝓞 L) L)ˣ → ℂ := fun c z => ∫ x in Ψ c, h (rep c) (x, z) ∂μ with hGc
  set bound : CC → (AdeleRing (𝓞 L) L)ˣ → ℝ := fun c z => (∫⁻ x in Ψ c, ‖h (rep c) (x, z)‖ₑ ∂μ).toReal
    with hbound
  have hGcm : ∀ c, AEStronglyMeasurable (Gc c) (νZ.restrict Ω) := fun c =>
    (((hcont (rep c)).stronglyMeasurable).integral_prod_left' (μ := μ.restrict (Ψ c))).aestronglyMeasurable
  have hGb : ∀ c, ∀ᵐ z ∂νZ.restrict Ω, ‖Gc c z‖ ≤ bound c z := fun c => Eventually.of_forall fun z => by
    simp only [hGc, hbound]
    refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
    simp only [ofReal_norm]
  have hbs : ∀ᵐ z ∂νZ.restrict Ω, Summable fun c => bound c z := hae.mono fun z hz => by
    refine ENNReal.summable_toReal ?_
    rw [(G1 z hz).1]; exact hz.ne
  have hbi : Integrable (fun z => ∑' c, bound c z) (νZ.restrict Ω) := by
    have hcongr : (fun z => (T z).toReal) =ᵐ[νZ.restrict Ω] fun z => ∑' c, bound c z := hae.mono fun z hz => by
      simp only [hbound]
      rw [← (G1 z hz).1, ENNReal.tsum_toReal_eq]
      intro c hc
      exact hz.ne ((G1 z hz).1 ▸ ENNReal.tsum_eq_top_of_eq_top ⟨c, hc⟩)
    refine Integrable.congr ?_ hcongr
    refine ⟨hTm.ennreal_toReal.aestronglyMeasurable, ?_⟩
    dsimp only [HasFiniteIntegral]
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hTfin
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  have hlim : ∀ᵐ z ∂νZ.restrict Ω, HasSum (fun c => Gc c z) (∫ x in Φ, ∑' δ : I, h δ (x, z) ∂Haar) :=
    hae.mono fun z hz => (G1 z hz).2.2
  have H3 : HasSum (fun c => ∫ z in Ω, Gc c z ∂νZ) (∫ z in Ω, (∫ x in Φ, ∑' δ : I, h δ (x, z) ∂Haar) ∂νZ) :=
    hasSum_integral_of_dominated_convergence bound hGcm hGb hbs hbi hlim

  have hprod_c : ∀ c : CC, Integrable (uncurry fun z x => h (rep c) (x, z))
      ((νZ.restrict Ω).prod (μ.restrict (Ψ c))) := by
    intro c
    have hcs : Continuous (uncurry fun z x => h (rep c) (x, z)) := (hcont (rep c)).comp continuous_swap
    refine ⟨hcs.aestronglyMeasurable, ?_⟩
    dsimp only [HasFiniteIntegral]
    rw [lintegral_prod (fun a => ‖uncurry (fun z x => h (rep c) (x, z)) a‖ₑ)
      hcs.measurable.enorm.aemeasurable]
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hTfin
    refine hae.mono fun z hz => ?_
    rw [← (G1 z hz).1]
    exact ENNReal.le_tsum c
  have hswap_c : ∀ c : CC, ∫ z in Ω, Gc c z ∂νZ = ∫ x in Ψ c, (∫ z in Ω, h (rep c) (x, z) ∂νZ) ∂μ := by
    intro c
    exact integral_integral_swap (hprod_c c)

  have hcontS : Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∑' δ : I, h δ p := continuous_tsum_hfun K L D σ hξc hφ hφc _
  have hprod : Integrable (uncurry fun z x => ∑' δ : I, h δ (x, z)) ((νZ.restrict Ω).prod (Haar.restrict Φ)) := by
    have hcs : Continuous (uncurry fun z x => ∑' δ : I, h δ (x, z)) := hcontS.comp continuous_swap
    refine ⟨hcs.aestronglyMeasurable, ?_⟩
    dsimp only [HasFiniteIntegral]
    rw [lintegral_prod (fun a => ‖uncurry (fun z x => ∑' δ : I, h δ (x, z)) a‖ₑ)
      hcs.measurable.enorm.aemeasurable]
    refine lt_of_le_of_lt ?_ hTfin
    refine lintegral_mono fun z => ?_
    exact lintegral_mono fun x => enorm_tsum_le_tsum_enorm
  have hswapS : ∫ z in Ω, (∫ x in Φ, ∑' δ : I, h δ (x, z) ∂Haar) ∂νZ =
      ∫ x in Φ, (∫ z in Ω, ∑' δ : I, h δ (x, z) ∂νZ) ∂Haar :=
    integral_integral_swap hprod

  have hfinal : ∫ x in Φ, (∫ z in Ω, ∑' δ : I, h δ (x, z) ∂νZ) ∂Haar =
      ∫ x in Φ, (∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | Q (LT.TwistedNorm.SigmaConjClasses.mk σ δ)},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            σA (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZ) ∂Haar := by
    congr 1; funext x; congr 1; funext z
    exact tsum_hfun_eq_mul_finsum K L D σ hφc _ (x, z)
  rw [hswapS, hfinal] at H3
  simp_rw [hswap_c] at H3
  exact H3

end Main

end R3TwFold

end

section
open MeasureTheory NumberField NumberField.AdelicHaar
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (α β : ℝ) (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZ : Measure (AdeleRing (𝓞 L) L)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (rep : LT.TwistedNorm.SigmaConjClasses σ → GL (Fin 2) L)
    (hrep : ∀ c, LT.TwistedNorm.SigmaConjClasses.mk σ (rep c) = c)
    (Ψ : LT.TwistedNorm.SigmaConjClasses σ → Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΨ : ∀ c : LT.TwistedNorm.SigmaConjClasses σ,
      (∃ γ : GL (Fin 2) K, (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen c = ConjClasses.mk γ) →
      IsFundamentalDomain
        ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (rep c)).map
          (AutomorphicForm.globalPoints (𝓞 L) L)) (Ψ c)
        ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
          {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (habs : ∫⁻ x in Φ, ∫⁻ z in Ω,
        ∑' δ : {δ : GL (Fin 2) L // ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
              ConjClasses.mk γ},
          ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))‖ₑ
          ∂νZ ∂(adelicGLHaar (Fin 2) (𝓞 L) L) < ⊤) :
    HasSum
      (fun c : {c : LT.TwistedNorm.SigmaConjClasses σ // ∃ γ : GL (Fin 2) K,
          (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
          LT.TwistedNorm.normClassMap hgen c = ConjClasses.mk γ} =>
        ∫ x in Ψ c, (∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L (rep c) *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZ)
          ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
            {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
      (∫ x in Φ, (∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
              (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
              LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
                ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZ)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) := by
  exact R3TwFold.main K L σ D α β Φ hΦs hΦ νZ Ω ξ hξc rep hrep Ψ
    (fun c => ∃ γ : GL (Fin 2) K,
      (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen c = ConjClasses.mk γ)
    hΨ φ hφ hφc habs

end

end S_AutomorphicForm_hasSum_setIntegral_setIntegral_twistedOrbital_of_normClass_elliptic_or_central
end P2MW
export P2MW.S_AutomorphicForm_hasSum_setIntegral_setIntegral_twistedOrbital_of_normClass_elliptic_or_central (solution)
