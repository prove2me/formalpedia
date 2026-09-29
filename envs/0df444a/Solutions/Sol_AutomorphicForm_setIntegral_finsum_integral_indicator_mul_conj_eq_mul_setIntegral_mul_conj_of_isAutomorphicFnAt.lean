-- Prove2me | solution 1 for AutomorphicForm.setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7e1a360f-ae77-5868-8e52-6d420244ff9e

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Theorems.Thm_AutomorphicForm_finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_exists_pos_forall_measure_inter_setOf_ideleNorm_mem_Icc_eq_ofReal_mul_log
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
open NumberField.TateGlobal
open scoped ENNReal

namespace Unfold25

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

theorem secondCountableTopology_units : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem secondCountableTopology_gl : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

theorem isHaarMeasure_glHaar : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

theorem countable_units : Countable Kˣ := by
  haveI : Countable K := Countable.of_equiv _ (Module.Free.chooseBasis ℚ K).equivFun.toEquiv.symm
  exact Function.Injective.countable (f := (Units.val : Kˣ → K)) Units.val_injective

theorem countable_gl : Countable (GL (Fin 2) K) := by
  haveI : Countable K := Countable.of_equiv _ (Module.Free.chooseBasis ℚ K).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) K → _)) Units.val_injective

theorem countable_quot : Countable (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) := by
  haveI := countable_gl K
  exact Function.Surjective.countable (QuotientGroup.mk_surjective)

theorem centralScalar_coe (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((centralScalar (𝓞 K) K z : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      (z : AdeleRing (𝓞 K) K) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
  show ((Units.map (Matrix.scalar (Fin 2)).toMonoidHom z : (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ˣ) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = _
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 K) K : (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have h1 : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ =>
        (z : AdeleRing (𝓞 K) K) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
      Units.continuous_val.smul continuous_const
    exact h1.congr fun z => (centralScalar_coe K z).symm
  · have h1 : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
      (Units.continuous_val.comp continuous_inv).smul continuous_const
    refine h1.congr fun z => ?_
    show _ = ((↑(centralScalar (𝓞 K) K z)⁻¹ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)))
    rw [← map_inv]
    exact (centralScalar_coe K z⁻¹).symm

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K z * g = g * centralScalar (𝓞 K) K z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, centralScalar_coe, smul_one_mul, Matrix.mul_smul, mul_one]

theorem det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z * z := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, centralScalar_coe, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin, Units.val_mul, pow_two]

theorem globalPoints_scalar_eq_centralScalar (a : Kˣ) :
    globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) := by
  apply Units.ext
  ext i j
  change algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (a : K)) i j) =
    (Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem injective_unitsMap :
    Function.Injective (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) := by
  haveI : Nontrivial (AdeleRing (𝓞 K) K) := by
    show Nontrivial (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)
    haveI : Nontrivial (InfiniteAdeleRing K) := by
      show Nontrivial ((w : InfinitePlace K) → w.Completion)
      letI : Inhabited (InfinitePlace K) := Classical.inhabited_of_nonempty inferInstance
      exact Pi.nontrivial
    infer_instance
  intro u v huv
  apply Units.ext
  have h := congrArg Units.val huv
  simp only [Units.coe_map, MonoidHom.coe_coe] at h
  exact (algebraMap K (AdeleRing (𝓞 K) K)).injective h

theorem injective_globalPoints : Function.Injective (globalPoints (𝓞 K) K) := by
  haveI : Nontrivial (AdeleRing (𝓞 K) K) := by
    show Nontrivial (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)
    haveI : Nontrivial (InfiniteAdeleRing K) := by
      show Nontrivial ((w : InfinitePlace K) → w.Completion)
      letI : Inhabited (InfinitePlace K) := Classical.inhabited_of_nonempty inferInstance
      exact Pi.nontrivial
    infer_instance
  intro γ γ' h
  apply Units.ext
  ext i j
  have := congrArg (fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) h
  exact (algebraMap K (AdeleRing (𝓞 K) K)).injective this

theorem ideleNorm_inv (t : (AdeleRing (𝓞 K) K)ˣ) : ideleNorm K t⁻¹ = (ideleNorm K t)⁻¹ := by
  have h1 : ideleNorm K (1 : (AdeleRing (𝓞 K) K)ˣ) = 1 := by
    have := ideleNorm_mul (1 : (AdeleRing (𝓞 K) K)ˣ) 1
    rw [one_mul] at this
    have hp := ideleNorm_pos (1 : (AdeleRing (𝓞 K) K)ˣ)
    field_simp at this
    nlinarith [this, hp]
  have := ideleNorm_mul t⁻¹ t
  rw [inv_mul_cancel, h1] at this
  have hp := ideleNorm_pos t
  field_simp
  linarith

def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {x | ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab K α β) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K α β

theorem globalPoints_mul_mem_slab_iff {α β : ℝ} (δ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    globalPoints (𝓞 K) K δ * g ∈ slab K α β ↔ g ∈ slab K α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem centralScalar_inv_mul_mem_slab_iff {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (t : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    (centralScalar (𝓞 K) K t)⁻¹ * g ∈ slab K α β ↔
      ideleNorm K t ∈ Set.Icc (Real.sqrt (ideleNorm K (Matrix.GeneralLinearGroup.det g) / β))
        (Real.sqrt (ideleNorm K (Matrix.GeneralLinearGroup.det g) / α)) := by
  have hu := ideleNorm_pos t
  have hdpos := ideleNorm_pos (Matrix.GeneralLinearGroup.det g)
  have hdet : Matrix.GeneralLinearGroup.det ((centralScalar (𝓞 K) K t)⁻¹ * g) =
      (t * t)⁻¹ * Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, map_inv, det_centralScalar]
  simp only [slab, Set.mem_setOf_eq, Set.mem_Icc]
  rw [hdet, ideleNorm_mul, ideleNorm_inv K, ideleNorm_mul]
  have hu2 : 0 < ideleNorm K t * ideleNorm K t := mul_pos hu hu
  rw [Real.sqrt_le_left hu.le, Real.le_sqrt hu.le (div_pos hdpos hα).le, pow_two,
    div_le_iff₀ (hα.trans hαβ), le_div_iff₀ hα, inv_mul_eq_div, le_div_iff₀ hu2, div_le_iff₀ hu2]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

theorem centralScalar_mem_setOf_iff {α β : ℝ} (hα : 0 < α) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β ↔
      ideleNorm K z ∈ Set.Icc (Real.sqrt α) (Real.sqrt β) := by
  have hu := ideleNorm_pos z
  rw [det_centralScalar, ideleNorm_mul, Set.mem_Icc, Set.mem_Icc]
  have hN : Real.sqrt (ideleNorm K z * ideleNorm K z) = ideleNorm K z := Real.sqrt_mul_self hu.le
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := Real.sqrt_le_sqrt h1; rwa [hN] at this
    · have := Real.sqrt_le_sqrt h2; rwa [hN] at this
  · rintro ⟨h1, h2⟩
    have hβ : 0 ≤ β := by
      have : 0 < Real.sqrt β := hu.trans_le h2
      exact (Real.sqrt_pos.1 this).le
    refine ⟨?_, ?_⟩
    · have := mul_self_le_mul_self (Real.sqrt_nonneg α) h1
      rwa [Real.mul_self_sqrt hα.le] at this
    · have := mul_self_le_mul_self hu.le h2
      rwa [Real.mul_self_sqrt hβ] at this

theorem scalar_injective : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL (Fin 2) K) := by
  intro a b h
  apply Units.ext
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simpa [Matrix.GeneralLinearGroup.scalar] using this

theorem exists_scalar_eq (δ : GL (Fin 2) K) :
    ∃ a : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) a = δ * ((QuotientGroup.mk δ : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)).out)⁻¹ := by
  have h : (QuotientGroup.mk ((QuotientGroup.mk δ : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)).out) :
      GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) = QuotientGroup.mk δ := QuotientGroup.out_eq' _
  rw [QuotientGroup.eq] at h
  obtain ⟨b, hb⟩ := (Matrix.GeneralLinearGroup.center_eq_range_scalar (n := Fin 2) (R := K)).le h
  refine ⟨b, ?_⟩
  have hcen : Matrix.GeneralLinearGroup.scalar (Fin 2) b ∈ Subgroup.center (GL (Fin 2) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨b, rfl⟩
  set o := ((QuotientGroup.mk δ : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)).out) with ho
  have e : δ = o * Matrix.GeneralLinearGroup.scalar (Fin 2) b := by
    rw [hb, mul_inv_cancel_left]
  have e2 := congrArg (fun t => t * o⁻¹) e
  rw [Subgroup.mem_center_iff.1 hcen, mul_inv_cancel_right] at e2
  exact e2.symm

noncomputable def repEquiv : (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) × Kˣ ≃ GL (Fin 2) K where
  toFun p := Matrix.GeneralLinearGroup.scalar (Fin 2) p.2 * p.1.out
  invFun δ := (QuotientGroup.mk δ, (exists_scalar_eq K δ).choose)
  left_inv := by
    rintro ⟨q, a⟩
    have hcen : Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ Subgroup.center (GL (Fin 2) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨a, rfl⟩
    have hmk : (QuotientGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * q.out) :
        GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) = q := by
      rw [← QuotientGroup.out_eq' q, eq_comm, QuotientGroup.eq, QuotientGroup.out_eq']
      rw [← Subgroup.mem_center_iff.1 hcen q.out, inv_mul_cancel_left]
      exact hcen
    show (_, _) = (q, a)
    refine Prod.ext hmk (scalar_injective K ?_)
    show Matrix.GeneralLinearGroup.scalar (Fin 2) (exists_scalar_eq K (Matrix.GeneralLinearGroup.scalar (Fin 2) a * q.out)).choose =
      Matrix.GeneralLinearGroup.scalar (Fin 2) a
    rw [(exists_scalar_eq K _).choose_spec, hmk, mul_inv_cancel_right]
  right_inv := by
    intro δ
    simp only
    rw [(exists_scalar_eq K δ).choose_spec, inv_mul_cancel_right]

theorem repEquiv_apply (q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) (a : Kˣ) :
    repEquiv K (q, a) = Matrix.GeneralLinearGroup.scalar (Fin 2) a * q.out := rfl

theorem tsum_tsum_eq_tsum_gl (Φ : GL (Fin 2) K → ℝ≥0∞) :
    ∑' q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K), ∑' a : Kˣ,
        Φ (Matrix.GeneralLinearGroup.scalar (Fin 2) a * q.out) = ∑' δ : GL (Fin 2) K, Φ δ := by
  rw [← ENNReal.tsum_prod, ← Equiv.tsum_eq (repEquiv K)]
  rfl

section StageA

variable (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
  (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
  (hΩK : IsFundamentalDomain
    (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
  (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦsub : Φ₀ ⊆ slab K α β)
  (hFD : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
    ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)))

include hΩK in

theorem omega_unfold (Φ : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) :
    ∫⁻ w, Φ w ∂νZK = ∑' a : Kˣ, ∫⁻ w in ΩK,
      Φ ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) a * w) ∂νZK := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  set ι := (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) with hι
  haveI := countable_units K
  haveI : Countable ι.range := (MonoidHom.rangeRestrict_surjective ι).countable
  rw [hΩK.lintegral_eq_tsum'' Φ]
  have hinj : Function.Injective ι := injective_unitsMap K
  rw [← Equiv.tsum_eq (MonoidHom.ofInjective hinj).toEquiv]
  rfl

theorem smulInvariantMeasure_restrict_slab :
    SMulInvariantMeasure (globalPoints (𝓞 K) K).range (AdelicGL2 (𝓞 K) K)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)) := by
  haveI := isHaarMeasure_glHaar K
  refine ⟨fun γ A hA => ?_⟩
  obtain ⟨δ, hδ⟩ := γ.2
  have hpre : (fun x : AdelicGL2 (𝓞 K) K => γ • x) ⁻¹' A = (fun x => globalPoints (𝓞 K) K δ * x) ⁻¹' A := by
    ext x; simp only [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, hδ]
  rw [hpre, Measure.restrict_apply' (measurableSet_slab K α β), Measure.restrict_apply' (measurableSet_slab K α β)]
  have : (fun x => globalPoints (𝓞 K) K δ * x) ⁻¹' A ∩ slab K α β =
      (fun x => globalPoints (𝓞 K) K δ * x) ⁻¹' (A ∩ slab K α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, globalPoints_mul_mem_slab_iff]
  rw [this, measure_preimage_mul]

include hΦsub hFD in

theorem gl_unfold (Φ : AdelicGL2 (𝓞 K) K → ℝ≥0∞) :
    ∫⁻ y in slab K α β, Φ y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∑' δ : GL (Fin 2) K, ∫⁻ g in Φ₀, Φ (globalPoints (𝓞 K) K δ * g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := secondCountableTopology_gl K
  haveI := isHaarMeasure_glHaar K
  haveI := countable_gl K
  haveI : Countable (globalPoints (𝓞 K) K).range := (MonoidHom.rangeRestrict_surjective _).countable
  haveI := smulInvariantMeasure_restrict_slab K α β
  have h := hFD.lintegral_eq_tsum'' Φ
  rw [h]
  have hinj := injective_globalPoints K
  rw [← Equiv.tsum_eq (MonoidHom.ofInjective hinj).toEquiv]
  refine tsum_congr fun δ => ?_
  rw [Measure.restrict_restrict' (measurableSet_slab K α β), Set.inter_eq_left.2 hΦsub]
  rfl

include hα hαβ hΩK in

theorem band_const (y : AdelicGL2 (𝓞 K) K) :
    νZK (ΩK ∩ {w | (centralScalar (𝓞 K) K w)⁻¹ * y ∈ slab K α β}) =
      νZK (ΩK ∩ {z | ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β}) := by
  obtain ⟨C, hC, hslab⟩ :=
    NumberField.TateGlobal.exists_pos_forall_measure_inter_setOf_ideleNorm_mem_Icc_eq_ofReal_mul_log K νZK
  set d : ℝ := ideleNorm K (Matrix.GeneralLinearGroup.det y) with hd
  have hdpos : 0 < d := ideleNorm_pos _
  have h1 : {w : (AdeleRing (𝓞 K) K)ˣ | (centralScalar (𝓞 K) K w)⁻¹ * y ∈ slab K α β} =
      {w | ideleNorm K w ∈ Set.Icc (Real.sqrt (d / β)) (Real.sqrt (d / α))} := by
    ext w; exact centralScalar_inv_mul_mem_slab_iff K hα hαβ w y
  have h2 : {z : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β} =
      {z | ideleNorm K z ∈ Set.Icc (Real.sqrt α) (Real.sqrt β)} := by
    ext z; exact centralScalar_mem_setOf_iff K hα z
  have ha : 0 < Real.sqrt (d / β) := Real.sqrt_pos.2 (div_pos hdpos (hα.trans hαβ))
  have hab : Real.sqrt (d / β) ≤ Real.sqrt (d / α) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hdpos.le hα hαβ.le)
  have ha' : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  have hab' : Real.sqrt α ≤ Real.sqrt β := Real.sqrt_le_sqrt hαβ.le
  rw [h1, h2, hslab ΩK hΩK _ _ ha hab, hslab ΩK hΩK _ _ ha' hab']
  congr 2
  have hβ : 0 < β := hα.trans hαβ
  have e1 : Real.sqrt (d / α) / Real.sqrt (d / β) = Real.sqrt (β / α) := by
    rw [← Real.sqrt_div' (d / α) (div_pos hdpos hβ).le]
    congr 1
    field_simp
  have e2 : Real.sqrt β / Real.sqrt α = Real.sqrt (β / α) := by
    rw [Real.sqrt_div' β hα.le]
  rw [e1, e2]

end StageA

section StageA2

variable (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
  (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
  (hΩK : IsFundamentalDomain
    (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
  (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦsub : Φ₀ ⊆ slab K α β)
  (hFD : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
    ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)))

include hα hαβ hΩK hΦsub hFD in

theorem stageA (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ g in Φ₀, ∑' q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
        ∫⁻ w, G (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g)) ∂νZK
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
    νZK (ΩK ∩ {z | ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β}) *
      ∫⁻ y, G y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  classical
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := secondCountableTopology_gl K
  haveI := isHaarMeasure_glHaar K
  haveI := countable_units K
  haveI := countable_gl K
  haveI := countable_quot K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set ι := (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) with hι
  set S := slab K α β with hS
  have hSm : MeasurableSet S := measurableSet_slab K α β

  have hGm : ∀ δ : GL (Fin 2) K, Measurable fun p : AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ =>
      G (centralScalar (𝓞 K) K p.2 * (globalPoints (𝓞 K) K δ * p.1)) := fun δ =>
    hG.comp (((continuous_centralScalar K).comp continuous_snd).mul (continuous_const.mul continuous_fst)).measurable
  have hGm' : ∀ δ : GL (Fin 2) K, Measurable fun p : (AdeleRing (𝓞 K) K)ˣ × AdelicGL2 (𝓞 K) K =>
      G (centralScalar (𝓞 K) K p.1 * (globalPoints (𝓞 K) K δ * p.2)) := fun δ =>
    hG.comp (((continuous_centralScalar K).comp continuous_fst).mul (continuous_const.mul continuous_snd)).measurable

  have hinner : ∀ g : AdelicGL2 (𝓞 K) K,
      ∑' q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
          ∫⁻ w, G (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g)) ∂νZK =
        ∑' δ : GL (Fin 2) K, ∫⁻ w in ΩK, G (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K δ * g)) ∂νZK := by
    intro g
    rw [← tsum_tsum_eq_tsum_gl K]
    refine tsum_congr fun q => ?_
    rw [omega_unfold K νZK ΩK hΩK]
    refine tsum_congr fun a => ?_
    refine lintegral_congr fun w => ?_
    congr 1
    rw [map_mul, map_mul, globalPoints_scalar_eq_centralScalar]
    simp only [mul_assoc]
    rw [← mul_assoc (centralScalar (𝓞 K) K (ι a)), centralScalar_comm K (ι a) (centralScalar (𝓞 K) K w), mul_assoc]
  simp_rw [hinner]

  have hmeas1 : ∀ δ : GL (Fin 2) K, AEMeasurable (fun g : AdelicGL2 (𝓞 K) K =>
      ∫⁻ w in ΩK, G (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K δ * g)) ∂νZK) (μ.restrict Φ₀) :=
    fun δ => ((hGm δ).lintegral_prod_right' (ν := νZK.restrict ΩK)).aemeasurable
  rw [lintegral_tsum hmeas1]
  have hswap : ∀ δ : GL (Fin 2) K,
      ∫⁻ g in Φ₀, ∫⁻ w in ΩK, G (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K δ * g)) ∂νZK ∂μ =
        ∫⁻ w in ΩK, ∫⁻ g in Φ₀, G (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K δ * g)) ∂μ ∂νZK :=
    fun δ => lintegral_lintegral_swap ((hGm δ).aemeasurable)
  simp_rw [hswap]
  have hmeas2 : ∀ δ : GL (Fin 2) K, AEMeasurable (fun w : (AdeleRing (𝓞 K) K)ˣ =>
      ∫⁻ g in Φ₀, G (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K δ * g)) ∂μ) (νZK.restrict ΩK) :=
    fun δ => ((hGm' δ).lintegral_prod_right' (ν := μ.restrict Φ₀)).aemeasurable
  rw [← lintegral_tsum hmeas2]

  have hgl : ∀ w : (AdeleRing (𝓞 K) K)ˣ,
      ∑' δ : GL (Fin 2) K, ∫⁻ g in Φ₀, G (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K δ * g)) ∂μ =
        ∫⁻ y in S, G (centralScalar (𝓞 K) K w * y) ∂μ :=
    fun w => (gl_unfold K α β Φ₀ hΦsub hFD (fun y => G (centralScalar (𝓞 K) K w * y))).symm
  simp_rw [hgl]

  have htrans : ∀ w : (AdeleRing (𝓞 K) K)ˣ,
      ∫⁻ y in S, G (centralScalar (𝓞 K) K w * y) ∂μ =
        ∫⁻ y, {w' : (AdeleRing (𝓞 K) K)ˣ | (centralScalar (𝓞 K) K w')⁻¹ * y ∈ S}.indicator 1 w * G y ∂μ := by
    intro w
    rw [← lintegral_indicator hSm]
    have := lintegral_mul_left_eq_self (μ := μ)
      (fun y => {w' : (AdeleRing (𝓞 K) K)ˣ | (centralScalar (𝓞 K) K w')⁻¹ * y ∈ S}.indicator 1 w * G y)
      (centralScalar (𝓞 K) K w)
    rw [← this]
    refine lintegral_congr fun y => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq, inv_mul_cancel_left, Pi.one_apply]
    split_ifs <;> simp
  simp_rw [htrans]

  have hmeas3 : AEMeasurable (Function.uncurry fun (w : (AdeleRing (𝓞 K) K)ˣ) (y : AdelicGL2 (𝓞 K) K) =>
      {w' : (AdeleRing (𝓞 K) K)ˣ | (centralScalar (𝓞 K) K w')⁻¹ * y ∈ S}.indicator 1 w * G y)
      ((νZK.restrict ΩK).prod μ) := by
    refine ((Measurable.indicator measurable_one ?_).mul (hG.comp measurable_snd)).aemeasurable
    exact hSm.preimage (((continuous_centralScalar K).comp continuous_fst).inv.mul continuous_snd).measurable
  rw [lintegral_lintegral_swap hmeas3]
  have hpull : ∀ y : AdelicGL2 (𝓞 K) K,
      ∫⁻ w in ΩK, {w' : (AdeleRing (𝓞 K) K)ˣ | (centralScalar (𝓞 K) K w')⁻¹ * y ∈ S}.indicator 1 w * G y ∂νZK =
        νZK (ΩK ∩ {z | ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β}) * G y := by
    intro y
    have hTm : MeasurableSet {w' : (AdeleRing (𝓞 K) K)ˣ | (centralScalar (𝓞 K) K w')⁻¹ * y ∈ S} :=
      hSm.preimage (((continuous_centralScalar K).inv).mul continuous_const).measurable
    rw [lintegral_mul_const _ ((measurable_one.indicator hTm)), lintegral_indicator_one hTm,
      Measure.restrict_apply hTm, Set.inter_comm, band_const K α β hα hαβ νZK ΩK hΩK y]
  simp_rw [hpull]
  rw [lintegral_const_mul _ hG]

end StageA2

section StageB

variable (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
  (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
  (hΩK : IsFundamentalDomain
    (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
  (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦsub : Φ₀ ⊆ slab K α β)
  (hFD : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
    ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)))

@[reducible] def quotMeasurableSpace : MeasurableSpace (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) := ⊤

attribute [local instance] quotMeasurableSpace

theorem quot_measurableSingletonClass : MeasurableSingletonClass (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

attribute [local instance] quot_measurableSingletonClass

noncomputable def theta (p : AdelicGL2 (𝓞 K) K × ((GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) × (AdeleRing (𝓞 K) K)ˣ)) :
    AdelicGL2 (𝓞 K) K :=
  centralScalar (𝓞 K) K p.2.2 * (globalPoints (𝓞 K) K p.2.1.out * p.1)

theorem measurable_theta : Measurable (theta K) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := secondCountableTopology_gl K
  haveI := countable_quot K
  have h1 : Measurable fun p : AdelicGL2 (𝓞 K) K × ((GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) ×
      (AdeleRing (𝓞 K) K)ˣ) => globalPoints (𝓞 K) K p.2.1.out :=
    (measurable_of_countable fun q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K) => globalPoints (𝓞 K) K q.out).comp
      (measurable_fst.comp measurable_snd)
  have h2 : Measurable fun p : AdelicGL2 (𝓞 K) K × ((GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) ×
      (AdeleRing (𝓞 K) K)ˣ) => centralScalar (𝓞 K) K p.2.2 :=
    (continuous_centralScalar K).measurable.comp (measurable_snd.comp measurable_snd)
  exact h2.mul (h1.mul measurable_fst)

noncomputable def prodMeasure : Measure (AdelicGL2 (𝓞 K) K × ((GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) ×
    (AdeleRing (𝓞 K) K)ˣ)) :=
  ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀).prod ((Measure.count).prod νZK)

noncomputable def bandConst : ℝ≥0∞ :=
  νZK (ΩK ∩ {z | ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})

include hα hαβ hΩK in
theorem bandConst_lt_top : bandConst K α β νZK ΩK < ⊤ := by
  obtain ⟨C, hC, hslab⟩ :=
    NumberField.TateGlobal.exists_pos_forall_measure_inter_setOf_ideleNorm_mem_Icc_eq_ofReal_mul_log K νZK
  have h2 : {z : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β} =
      {z | ideleNorm K z ∈ Set.Icc (Real.sqrt α) (Real.sqrt β)} := by
    ext z; exact centralScalar_mem_setOf_iff K hα z
  unfold bandConst
  rw [h2, hslab ΩK hΩK _ _ (Real.sqrt_pos.2 hα) (Real.sqrt_le_sqrt hαβ.le)]
  exact ENNReal.ofReal_lt_top

include hα hαβ hΩK hΦsub hFD in

theorem map_theta :
    (prodMeasure K νZK Φ₀).map (theta K) = bandConst K α β νZK ΩK • adelicGLHaar (Fin 2) (𝓞 K) K := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := secondCountableTopology_gl K
  haveI := isHaarMeasure_glHaar K
  haveI := countable_quot K
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_theta K) hA, Measure.smul_apply, smul_eq_mul]
  unfold prodMeasure
  rw [← lintegral_indicator_one (hA.preimage (measurable_theta K)),
    lintegral_prod _ ((measurable_one.indicator (hA.preimage (measurable_theta K))).aemeasurable)]
  have hinner : ∀ g : AdelicGL2 (𝓞 K) K,
      ∫⁻ p : (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) × (AdeleRing (𝓞 K) K)ˣ,
          ((theta K) ⁻¹' A).indicator (1 : AdelicGL2 (𝓞 K) K × ((GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) × (AdeleRing (𝓞 K) K)ˣ) → ℝ≥0∞) (g, p) ∂((Measure.count).prod νZK) =
        ∑' q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
          ∫⁻ w, A.indicator 1 (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g)) ∂νZK := by
    intro g
    have hm : Measurable fun p : (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) × (AdeleRing (𝓞 K) K)ˣ =>
        ((theta K) ⁻¹' A).indicator (1 : AdelicGL2 (𝓞 K) K × ((GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) × (AdeleRing (𝓞 K) K)ˣ) → ℝ≥0∞) (g, p) :=
      (measurable_one.indicator (hA.preimage (measurable_theta K))).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ hm.aemeasurable, lintegral_count]
    refine tsum_congr fun q => lintegral_congr fun w => ?_
    rfl
  simp_rw [hinner]
  rw [stageA K α β hα hαβ νZK ΩK hΩK Φ₀ hΦsub hFD (A.indicator 1) (measurable_one.indicator hA),
    lintegral_indicator_one hA]
  rfl

include hα hαβ hΩK hΦsub hFD in

theorem integral_theta (F : AdelicGL2 (𝓞 K) K → ℂ) (hF : Integrable F (adelicGLHaar (Fin 2) (𝓞 K) K)) :
    Integrable (F ∘ theta K) (prodMeasure K νZK Φ₀) ∧
    ∫ p, F (theta K p) ∂(prodMeasure K νZK Φ₀) =
      ((bandConst K α β νZK ΩK).toReal : ℂ) * ∫ y, F y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have hmap := map_theta K α β hα hαβ νZK ΩK hΩK Φ₀ hΦsub hFD
  have hb := bandConst_lt_top K α β hα hαβ νZK ΩK hΩK
  have hFb : Integrable F (bandConst K α β νZK ΩK • adelicGLHaar (Fin 2) (𝓞 K) K) := hF.smul_measure hb.ne
  have hFm : AEStronglyMeasurable F ((prodMeasure K νZK Φ₀).map (theta K)) := by
    rw [hmap]; exact hFb.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · rw [← integrable_map_measure hFm (measurable_theta K).aemeasurable, hmap]
    exact hFb
  · rw [← integral_map (measurable_theta K).aemeasurable hFm, hmap, integral_smul_measure, Complex.real_smul]

end StageB

section StageC

attribute [local instance] quotMeasurableSpace quot_measurableSingletonClass

variable [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
  (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
  (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)

theorem ae_ae_not_mem (N : Set (AdelicGL2 (𝓞 K) K)) (hNm : MeasurableSet N) (hN : adelicGLHaar (Fin 2) (𝓞 K) K N = 0)
    (q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), ∀ᵐ w ∂νZK,
      centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g) ∉ N := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := secondCountableTopology_gl K
  haveI := isHaarMeasure_glHaar K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Sq : Set (AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ) :=
    {p | centralScalar (𝓞 K) K p.2 * (globalPoints (𝓞 K) K q.out * p.1) ∈ N} with hSq
  have hSqm : MeasurableSet Sq :=
    hNm.preimage (((continuous_centralScalar K).comp continuous_snd).mul
      (continuous_const.mul continuous_fst)).measurable
  have hnull : (μ.prod νZK) Sq = 0 := by
    rw [Measure.prod_apply_symm hSqm]
    have : ∀ w : (AdeleRing (𝓞 K) K)ˣ, μ ((fun g => (g, w)) ⁻¹' Sq) = 0 := by
      intro w
      have : (fun g => (g, w)) ⁻¹' Sq =
          (fun g => (centralScalar (𝓞 K) K w * globalPoints (𝓞 K) K q.out) * g) ⁻¹' N := by
        ext g; simp only [hSq, Set.mem_preimage, Set.mem_setOf_eq, mul_assoc]
      rw [this, measure_preimage_mul, hN]
    simp [this]
  exact Measure.ae_ae_of_ae_prod (measure_eq_zero_iff_ae_notMem.1 hnull)

variable (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)

include hξu in

theorem xi_inv_eq_conj (w : (AdeleRing (𝓞 K) K)ˣ) :
    (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) = conj ((ξK ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) := by
  rw [Units.val_inv_eq_inv_val, Complex.inv_def, Complex.normSq_eq_norm_sq, hξu w, one_pow, inv_one,
    Complex.ofReal_one, mul_one]

theorem main
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (Ψ : AdelicGL2 (𝓞 K) K → ℂ) (hΨm : Measurable Ψ)
    (hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0)
    (hΨb : ∃ B : ℝ, ∀ y, ‖Ψ y‖ ≤ B)
    (u : AdelicGL2 (𝓞 K) K → ℂ)
    (hul : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), u (globalPoints (𝓞 K) K γ * g) = u g)
    (huc : ∀ (w : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      u (centralScalar (𝓞 K) K w * g) = ((ξK ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) * u g)
    (hu2 : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (canonicalTruncationDomain K α β))) :
    ∫ g in canonicalTruncationDomain K α β,
        (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (canonicalTruncationDomain K α β).indicator Ψ
                (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (u g)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((νZK (ΩK ∩ {z | ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
        ∫ g in canonicalTruncationDomain K α β, Ψ g * conj (u g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  classical
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := secondCountableTopology_gl K
  haveI := isHaarMeasure_glHaar K
  haveI := countable_quot K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ₀ := canonicalTruncationDomain K α β with hΦ₀

  by_cases hdat : ∃ d, IsTruncationDatum K α β d
  swap
  · have hempty : Φ₀ = ∅ := by
      show (canonicalTruncationData K α β).2.2 = ∅
      unfold canonicalTruncationData
      rw [dif_neg hdat]
    rw [hempty, Measure.restrict_empty, integral_zero_measure, integral_zero_measure, mul_zero]
  obtain ⟨-, -, -, hsub, hFD⟩ := canonicalTruncationData_spec K hdat
  change Φ₀ ⊆ slab K α β at hsub
  change IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ (μ.restrict (slab K α β)) at hFD
  obtain ⟨CΨ, hCΨ, hΨC⟩ := hΨc
  obtain ⟨BΨ, hΨB⟩ := hΨb

  have hΦ₀nm : NullMeasurableSet Φ₀ μ := by
    obtain ⟨s', hsub', hs'm, hs'ae⟩ := hFD.nullMeasurableSet.exists_measurable_superset_ae_eq
    have hSm := measurableSet_slab K α β
    have h1 : (μ.restrict (slab K α β)) (s' \ Φ₀) = 0 := (ae_eq_set.1 hs'ae).1
    rw [Measure.restrict_apply' hSm] at h1
    have hae : Φ₀ =ᵐ[μ] (s' ∩ slab K α β : Set _) := by
      rw [ae_eq_set]
      constructor
      · have : Φ₀ \ (s' ∩ slab K α β) = ∅ := Set.diff_eq_empty.2 fun y hy => ⟨hsub' hy, hsub hy⟩
        rw [this, measure_empty]
      · refine measure_mono_null ?_ h1
        intro y hy; exact ⟨⟨hy.1.1, hy.2⟩, hy.1.2⟩
    exact (hs'm.inter hSm).nullMeasurableSet.congr hae.symm
  obtain ⟨Φ₁, -, hΦ₁m, hae⟩ := hΦ₀nm.exists_measurable_superset_ae_eq

  have hres : μ.restrict Φ₁ = μ.restrict Φ₀ := Measure.restrict_congr_set hae
  set Ψ₁ := Φ₁.indicator Ψ with hΨ₁
  have hΨ₁m : Measurable Ψ₁ := hΨm.indicator hΦ₁m
  set F₁ : AdelicGL2 (𝓞 K) K → ℂ := fun h => Ψ₁ h * conj (u h) with hF₁

  have hF₁i : Integrable F₁ μ := by
    have hfin : μ (Φ₁ ∩ CΨ) < ⊤ := lt_of_le_of_lt (measure_mono Set.inter_subset_right) hCΨ.measure_lt_top
    haveI : IsFiniteMeasure (μ.restrict (Φ₁ ∩ CΨ)) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
    have hu2' : MemLp u 2 (μ.restrict (Φ₁ ∩ CΨ)) := by
      have := (hres.symm ▸ hu2 : MemLp u 2 (μ.restrict Φ₁)).restrict CΨ
      rwa [Measure.restrict_restrict hCΨ.measurableSet, Set.inter_comm] at this
    have hui : Integrable u (μ.restrict (Φ₁ ∩ CΨ)) := hu2'.integrable one_le_two
    have huci : Integrable (fun h => conj (u h)) (μ.restrict (Φ₁ ∩ CΨ)) :=
      (Complex.conjCLE.toContinuousLinearMap.integrable_comp hui :)
    have hprod : Integrable (fun h => Ψ h * conj (u h)) (μ.restrict (Φ₁ ∩ CΨ)) :=
      huci.bdd_mul hΨm.aestronglyMeasurable (Filter.Eventually.of_forall hΨB)
    have heq : F₁ = (Φ₁ ∩ CΨ).indicator fun h => Ψ h * conj (u h) := by
      funext h
      simp only [hF₁, hΨ₁, Set.indicator_apply, Set.mem_inter_iff]
      by_cases h1 : h ∈ Φ₁
      · by_cases h2 : h ∈ CΨ
        · simp [h1, h2]
        · simp [h1, h2, hΨC h h2]
      · simp [h1]
    rw [heq, integrable_indicator_iff (hΦ₁m.inter hCΨ.measurableSet)]
    exact hprod

  obtain ⟨hint, hval⟩ := integral_theta K α β hα hαβ νZK ΩK hΩK Φ₀ hsub hFD F₁ hF₁i

  have hnull : μ ((Φ₁ \ Φ₀) ∪ (Φ₀ \ Φ₁)) = 0 := by
    have h := ae_eq_set.1 hae; exact measure_union_null h.1 h.2
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hnull
  have hind : ∀ y ∉ N, Φ₀.indicator Ψ y = Ψ₁ y := by
    intro y hy
    have h1' : y ∈ Φ₀ → y ∈ Φ₁ := fun h => by
      by_contra h'; exact hy (hNsub (Or.inr ⟨h, h'⟩))
    have h2' : y ∈ Φ₁ → y ∈ Φ₀ := fun h => by
      by_contra h'; exact hy (hNsub (Or.inl ⟨h, h'⟩))
    simp only [hΨ₁, Set.indicator_apply]
    by_cases h1 : y ∈ Φ₀
    · rw [if_pos h1, if_pos (h1' h1)]
    · rw [if_neg h1, if_neg (fun h => h1 (h2' h))]
  have hgood : ∀ᵐ g ∂μ, ∀ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K), ∀ᵐ w ∂νZK,
      centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g) ∉ N :=
    ae_all_iff.2 fun q => ae_ae_not_mem K νZK N hNm hN0 q

  have hθ : ∀ g : AdelicGL2 (𝓞 K) K,
      (∀ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K), ∀ᵐ w ∂νZK,
        centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g) ∉ N) →
      (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
          ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
            Φ₀.indicator Ψ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g)) ∂νZK) * conj (u g) =
        ∑' q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
          ∫ w, F₁ (theta K (g, (q, w))) ∂νZK := by
    intro g hg

    have hterm : ∀ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
        (∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
            Φ₀.indicator Ψ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g)) ∂νZK) * conj (u g) =
          ∫ w, F₁ (theta K (g, (q, w))) ∂νZK := by
      intro q
      rw [← integral_mul_const]
      refine integral_congr_ae ((hg q).mono fun w hw => ?_)
      simp only [hF₁, theta]
      rw [hind _ hw, huc, hul, map_mul, xi_inv_eq_conj K ξK hξu]
      ring

    have hfin : (Function.support fun q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K) =>
        ∫ w, F₁ (theta K (g, (q, w))) ∂νZK).Finite := by
      have hQ := AutomorphicForm.finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact
        K CΨ {1} {g} hCΨ isCompact_singleton isCompact_singleton
      refine hQ.subset fun q hq => ?_
      rw [Function.mem_support] at hq
      by_contra hnot
      apply hq
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun w => ?_)
      have : Ψ₁ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g)) = 0 := by
        simp only [hΨ₁, Set.indicator_apply_eq_zero]
        intro _
        apply hΨC
        intro hmem
        exact hnot ⟨1, rfl, g, rfl, w, by rw [inv_one, one_mul, ← mul_assoc, ← centralScalar_comm, mul_assoc]; exact hmem⟩
      simp only [hF₁, theta, this, zero_mul, Pi.zero_apply]
    rw [tsum_eq_finsum hfin, finsum_mul]
    exact finsum_congr hterm

  have hL1 : ∫ g in Φ₀, (fun g : AdelicGL2 (𝓞 K) K =>
        ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
          ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
            Φ₀.indicator Ψ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (u g) ∂μ =
      ∫ g in Φ₀, ∑' q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
          ∫ w, F₁ (theta K (g, (q, w))) ∂νZK ∂μ := by
    refine integral_congr_ae ((ae_restrict_of_ae hgood).mono fun g hg => ?_)
    exact hθ g hg
  have hL2 : ∫ g in Φ₀, ∑' q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
          ∫ w, F₁ (theta K (g, (q, w))) ∂νZK ∂μ =
      ∫ g in Φ₀, ∫ p, F₁ (theta K (g, p)) ∂((Measure.count).prod νZK) ∂μ := by
    have hsec := hint.prod_right_ae
    refine integral_congr_ae (hsec.mono fun g hg => ?_)
    have hg' : Integrable (fun p : (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) × (AdeleRing (𝓞 K) K)ˣ =>
        F₁ (theta K (g, p))) ((Measure.count).prod νZK) := hg
    dsimp only
    rw [integral_prod _ hg', integral_countable' hg'.integral_prod_left]
    refine tsum_congr fun q => ?_
    have h1 : (Measure.count : Measure (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K))).real {q} = 1 := by
      simp [Measure.real, Measure.count_singleton]
    rw [h1, one_smul]
  have hL3 : ∫ g in Φ₀, ∫ p, F₁ (theta K (g, p)) ∂((Measure.count).prod νZK) ∂μ =
      ∫ z, F₁ (theta K z) ∂(prodMeasure K νZK Φ₀) := (integral_prod _ hint).symm
  have hL5 : ∫ y, F₁ y ∂μ = ∫ g in Φ₀, Ψ g * conj (u g) ∂μ := by
    rw [← hres, ← integral_indicator hΦ₁m]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only [hF₁, hΨ₁]
    exact (Set.indicator_mul_left Φ₁ Ψ (fun h => conj (u h))).symm
  rw [hL1, hL2, hL3, hval, hL5]
  rfl

end StageC

end Unfold25

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨm : Measurable Ψ)
    (_hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0)
    (_hΨb : ∃ B : ℝ, ∀ y, ‖Ψ y‖ ≤ B)
    (u : AdelicGL2 (𝓞 K) K → ℂ)
    (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u) :
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (u g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, Ψ g * conj (u g)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have h := (AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξK
    (AutomorphicForm.canonicalTruncationDomain K α β) u).1 _hu
  exact Unfold25.main K νZK ξK α β hα hαβ ΩK hΩK hξc hξt hξu Ψ _hΨm _hΨc _hΨb u
    (fun γ g => h.1.left_invariant γ g) (fun w g => h.1.central_transform ⟨w, Subgroup.mem_top w⟩ g) h.2

end S_AutomorphicForm_setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt (solution)
