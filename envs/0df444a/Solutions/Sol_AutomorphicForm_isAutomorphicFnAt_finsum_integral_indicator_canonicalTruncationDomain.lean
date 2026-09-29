-- Prove2me | solution 1 for AutomorphicForm.isAutomorphicFnAt_finsum_integral_indicator_canonicalTruncationDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3fc9c235-c934-53cf-8b0b-2830543f7cc8

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
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_mem_of_inv_mul_globalPoints_mul_centralScalar_mul_mem_of_isCompact
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isAutomorphicFnAt_finsum_integral_indicator_canonicalTruncationDomain
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace ThetaAut19

noncomputable section

open AutomorphicForm Filter

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

theorem countable_quot : Countable (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) := by
  haveI : Countable K := by
    haveI : Countable K := Countable.of_equiv _ (Module.Free.chooseBasis ℚ K).equivFun.toEquiv.symm
    infer_instance
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (GL (Fin 2) K) :=
    Function.Injective.countable (f := (Units.val : GL (Fin 2) K → _)) Units.val_injective
  exact Function.Surjective.countable (QuotientGroup.mk_surjective)

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K z * g = g * centralScalar (𝓞 K) K z := by
  have : centralScalar (𝓞 K) K z ∈ Subgroup.center (AdelicGL2 (𝓞 K) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨z, rfl⟩
  exact ((Subgroup.mem_center_iff.mp this) g).symm

theorem centralScalar_swap (a b : (AdeleRing (𝓞 K) K)ˣ) :
    centralScalar (𝓞 K) K a * centralScalar (𝓞 K) K b = centralScalar (𝓞 K) K b * centralScalar (𝓞 K) K a := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem globalPoints_scalar_eq_centralScalar (a : Kˣ) :
    globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) := by
  apply Units.ext
  ext i j
  change algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (a : K)) i j) =
    (Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem exists_out_mk_eq (δ : GL (Fin 2) K) :
    ∃ a : Kˣ, (QuotientGroup.mk δ : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)).out =
      δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin 2) K)) δ
  obtain ⟨a, ha⟩ := (Matrix.GeneralLinearGroup.center_eq_range_scalar (n := Fin 2) (R := K)).le h.2
  exact ⟨a, by rw [hh, ← ha]⟩

theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 K) K : (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K) := by
  have hcoe : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((centralScalar (𝓞 K) K z : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
        (z : AdeleRing (𝓞 K) K) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    intro z
    show ((Units.map (Matrix.scalar (Fin 2)).toMonoidHom z : (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ˣ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = _
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (Units.continuous_val.smul continuous_const).congr fun z => (hcoe z).symm
  · refine ((Units.continuous_val.comp continuous_inv).smul
      (continuous_const (y := (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))))).congr fun z => ?_
    show _ = ((↑(centralScalar (𝓞 K) K z)⁻¹ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)))
    rw [← map_inv]
    exact (hcoe z⁻¹).symm

section Fold

variable [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
  (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
  (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)

def term (Ψ' : AdelicGL2 (𝓞 K) K → ℂ) (δ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
    Ψ' (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K δ * g)) ∂νZK

def theta (Ψ' : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K), term K νZK ξK Ψ' q.out g

theorem theta_def (Ψ' : AdelicGL2 (𝓞 K) K → ℂ) :
    theta K νZK ξK Ψ' = fun g => ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
      ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
        Ψ' (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g)) ∂νZK := rfl

variable (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
    z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
      ξK ⟨z, Subgroup.mem_top z⟩ = 1)

theorem term_globalPoints_mul (Ψ' : AdelicGL2 (𝓞 K) K → ℂ) (δ γ' : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    term K νZK ξK Ψ' δ (globalPoints (𝓞 K) K γ' * g) = term K νZK ξK Ψ' (δ * γ') g := by
  simp only [term, map_mul, mul_assoc]

include hξt in

theorem term_mul_scalar (Ψ' : AdelicGL2 (𝓞 K) K → ℂ) (δ : GL (Fin 2) K) (a : Kˣ)
    (g : AdelicGL2 (𝓞 K) K) :
    term K νZK ξK Ψ' (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a) g = term K νZK ξK Ψ' δ g := by
  set ιa := (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) a with hιa
  have hξa : ξK ⟨ιa, Subgroup.mem_top ιa⟩ = 1 := hξt ιa ⟨a, rfl⟩
  simp only [term]
  rw [map_mul, globalPoints_scalar_eq_centralScalar]
  have harg : ∀ w : (AdeleRing (𝓞 K) K)ˣ,
      centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K δ * centralScalar (𝓞 K) K ιa * g) =
        centralScalar (𝓞 K) K (ιa * w) * (globalPoints (𝓞 K) K δ * g) := by
    intro w
    rw [← centralScalar_comm K ιa (globalPoints (𝓞 K) K δ)]
    simp only [← mul_assoc, map_mul]
    rw [centralScalar_swap K w ιa]
  have hxi : ∀ w : (AdeleRing (𝓞 K) K)ˣ, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) =
      (((ξK ⟨ιa * w, Subgroup.mem_top _⟩)⁻¹ : ℂˣ) : ℂ) := by
    intro w
    have : (⟨ιa * w, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) =
        ⟨ιa, Subgroup.mem_top ιa⟩ * ⟨w, Subgroup.mem_top w⟩ := rfl
    rw [this, map_mul, hξa, one_mul]
  rw [← integral_mul_left_eq_self
    (fun w : (AdeleRing (𝓞 K) K)ˣ => (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
      Ψ' (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K δ * g))) ιa]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  rw [harg w, hxi w]

include hξt in
theorem term_out_mk (Ψ' : AdelicGL2 (𝓞 K) K → ℂ) (δ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    term K νZK ξK Ψ' (QuotientGroup.mk δ : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)).out g =
      term K νZK ξK Ψ' δ g := by
  obtain ⟨a, ha⟩ := exists_out_mk_eq K δ
  rw [ha, term_mul_scalar K νZK ξK hξt]

include hξt in

theorem theta_globalPoints_mul (Ψ' : AdelicGL2 (𝓞 K) K → ℂ) (γ' : GL (Fin 2) K)
    (g : AdelicGL2 (𝓞 K) K) :
    theta K νZK ξK Ψ' (globalPoints (𝓞 K) K γ' * g) = theta K νZK ξK Ψ' g := by
  simp only [theta]
  rw [← finsum_comp_equiv (Equiv.mulRight
    (QuotientGroup.mk γ' : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)))
    (f := fun q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K) => term K νZK ξK Ψ' q.out g)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_mulRight]
  rw [term_globalPoints_mul]
  have hq : q * (QuotientGroup.mk γ' : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) =
      QuotientGroup.mk (q.out * γ') := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [hq, term_out_mk K νZK ξK hξt]

theorem term_centralScalar_mul (Ψ' : AdelicGL2 (𝓞 K) K → ℂ) (δ : GL (Fin 2) K)
    (a : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    term K νZK ξK Ψ' δ (centralScalar (𝓞 K) K a * g) =
      ((ξK ⟨a, Subgroup.mem_top a⟩ : ℂˣ) : ℂ) * term K νZK ξK Ψ' δ g := by
  simp only [term]
  have harg : ∀ w : (AdeleRing (𝓞 K) K)ˣ,
      centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K δ * (centralScalar (𝓞 K) K a * g)) =
        centralScalar (𝓞 K) K (a * w) * (globalPoints (𝓞 K) K δ * g) := by
    intro w
    rw [← mul_assoc (globalPoints (𝓞 K) K δ), ← centralScalar_comm K a (globalPoints (𝓞 K) K δ)]
    simp only [← mul_assoc, map_mul]
    rw [centralScalar_swap K w a]
  have hxi : ∀ w : (AdeleRing (𝓞 K) K)ˣ, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) =
      ((ξK ⟨a, Subgroup.mem_top a⟩ : ℂˣ) : ℂ) * (((ξK ⟨a * w, Subgroup.mem_top _⟩)⁻¹ : ℂˣ) : ℂ) := by
    intro w
    have : (⟨a * w, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) =
        ⟨a, Subgroup.mem_top a⟩ * ⟨w, Subgroup.mem_top w⟩ := rfl
    rw [this, map_mul, mul_inv, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  rw [← integral_mul_left_eq_self
    (fun w : (AdeleRing (𝓞 K) K)ˣ => (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
      Ψ' (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K δ * g))) a, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  rw [harg w, hxi w, mul_assoc]

theorem theta_centralScalar_mul (Ψ' : AdelicGL2 (𝓞 K) K → ℂ) (a : (AdeleRing (𝓞 K) K)ˣ)
    (g : AdelicGL2 (𝓞 K) K) :
    theta K νZK ξK Ψ' (centralScalar (𝓞 K) K a * g) =
      ((ξK ⟨a, Subgroup.mem_top a⟩ : ℂˣ) : ℂ) * theta K νZK ξK Ψ' g := by
  simp only [theta, term_centralScalar_mul]
  rw [mul_finsum]

include hξt in
theorem isLsXiFunction_theta (Ψ' : AdelicGL2 (𝓞 K) K → ℂ) :
    IsLsXiFunction (𝓞 K) K ⊤ ξK (theta K νZK ξK Ψ') :=
  ⟨fun γ' g => theta_globalPoints_mul K νZK ξK hξt Ψ' γ' g,
   fun z g => theta_centralScalar_mul K νZK ξK Ψ' z g⟩

variable (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)

include hξt hξu in

theorem theta_bounded (Ψ' : AdelicGL2 (𝓞 K) K → ℂ) (C : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C)
    (hΨC : ∀ y ∉ C, Ψ' y = 0) (B : ℝ) (hB : ∀ y, ‖Ψ' y‖ ≤ B) :
    ∃ M : ℝ, ∀ g, ‖theta K νZK ξK Ψ' g‖ ≤ M := by
  classical
  have hB0 : 0 ≤ B := by
    by_cases hne : C.Nonempty
    · obtain ⟨y, -⟩ := hne; exact (norm_nonneg _).trans (hB y)
    · exact (norm_nonneg (Ψ' 1)).trans (hB 1)

  have hQfin := AutomorphicForm.finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact
    K C {1} C hC isCompact_singleton hC
  set Q : Finset (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) := hQfin.toFinset with hQ

  have hS : ∀ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K), ∃ S : Set (AdeleRing (𝓞 K) K)ˣ,
      IsCompact S ∧ ∀ w : (AdeleRing (𝓞 K) K)ˣ, ∀ h ∈ C,
        Ψ' (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * h)) ≠ 0 → w ∈ S := by
    intro q
    obtain ⟨S, hSc, hSw⟩ :=
      AutomorphicForm.exists_isCompact_forall_mem_of_inv_mul_globalPoints_mul_centralScalar_mul_mem_of_isCompact
        K C {1} C hC isCompact_singleton hC q.out
    refine ⟨S, hSc, fun w h hh hΨ => hSw w ⟨1, rfl, h, hh, ?_⟩⟩
    rw [inv_one, one_mul, ← mul_assoc, ← centralScalar_comm, mul_assoc]
    by_contra h'; exact hΨ (hΨC _ h')
  choose S hSc hSw using hS
  set M : ℝ := ∑ q ∈ Q, B * (νZK (S q)).toReal with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun q _ => mul_nonneg hB0 ENNReal.toReal_nonneg

  have hterm : ∀ q, ∀ h ∈ C, ‖term K νZK ξK Ψ' q.out h‖ ≤ B * (νZK (S q)).toReal := by
    intro q h hh
    simp only [term]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S q) (fun w hw => ?_)]
    · refine norm_setIntegral_le_of_norm_le_const (hSc q).measure_lt_top (fun w _ => ?_)
      rw [norm_mul, Units.val_inv_eq_inv_val, norm_inv, hξu, inv_one, one_mul]
      exact hB _
    · have : Ψ' (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * h)) = 0 := by
        by_contra hne; exact hw (hSw q w h hh hne)
      rw [this, mul_zero]
  have hsupp : ∀ h ∈ C, (Function.support fun q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K) =>
      term K νZK ξK Ψ' q.out h) ⊆ ↑Q := by
    intro h hh q hq
    rw [Function.mem_support] at hq
    rw [Finset.mem_coe, hQ, Set.Finite.mem_toFinset]
    by_contra hqQ
    apply hq
    simp only [term]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun w => ?_)
    have : Ψ' (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * h)) = 0 := by
      by_contra hne
      refine hqQ ⟨1, rfl, h, hh, w, ?_⟩
      rw [inv_one, one_mul, ← mul_assoc, ← centralScalar_comm, mul_assoc]
      by_contra h'; exact hne (hΨC _ h')
    simp [this]
  have honC : ∀ h ∈ C, ‖theta K νZK ξK Ψ' h‖ ≤ M := by
    intro h hh
    simp only [theta]
    rw [finsum_eq_sum_of_support_subset _ (hsupp h hh)]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hterm q h hh)

  refine ⟨M, fun g => ?_⟩
  by_cases h0 : theta K νZK ξK Ψ' g = 0
  · rw [h0, norm_zero]; exact hM0

  obtain ⟨q, hq⟩ : ∃ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K), term K νZK ξK Ψ' q.out g ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h0 (by simp only [theta]; exact finsum_eq_zero_of_forall_eq_zero hall)
  obtain ⟨w, hw⟩ : ∃ w : (AdeleRing (𝓞 K) K)ˣ,
      Ψ' (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g)) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hq
    simp only [term]
    exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun w => by simp [hall w])
  have hmem : centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g) ∈ C := by
    by_contra h'; exact hw (hΨC _ h')
  have key := honC _ hmem
  rw [theta_centralScalar_mul, theta_globalPoints_mul K νZK ξK hξt, norm_mul, hξu, one_mul] at key
  exact key

omit [BorelSpace (AdeleRing (𝓞 K) K)ˣ] [νZK.IsHaarMeasure] in

theorem measurable_finsum_of_countable {X Q : Type*} [MeasurableSpace X] [Countable Q]
    (T : Q → X → ℂ) (hT : ∀ q, Measurable (T q))
    (hfin : ∀ x, (Function.support fun q => T q x).Finite) :
    Measurable fun x => ∑ᶠ q, T q x := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat Q
  let s : ℕ → Finset Q := fun n => (Finset.range n).preimage e (he.injOn)
  have hs : ∀ x, ∀ᶠ n in atTop, (∑ q ∈ s n, T q x) = ∑ᶠ q, T q x := by
    intro x
    refine eventually_atTop.2 ⟨(hfin x).toFinset.sup e + 1, fun n hn => ?_⟩
    refine (finsum_eq_sum_of_support_subset _ fun q hq => ?_).symm
    rw [Finset.mem_coe, Finset.mem_preimage, Finset.mem_range]
    have : e q ≤ (hfin x).toFinset.sup e := Finset.le_sup ((hfin x).mem_toFinset.2 hq)
    omega
  refine measurable_of_tendsto_metrizable (f := fun n x => ∑ q ∈ s n, T q x)
    (fun n => Finset.measurable_sum _ fun q _ => hT q) ?_
  rw [tendsto_pi_nhds]
  intro x
  exact (tendsto_congr' (hs x)).mpr tendsto_const_nhds

variable (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))

include hξc in
theorem continuous_xi_inv :
    Continuous fun w : (AdeleRing (𝓞 K) K)ˣ => (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) := by
  have : (fun w : (AdeleRing (𝓞 K) K)ˣ => (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ)) =
      fun w => (((ξK ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ))⁻¹ := by
    funext w; rw [Units.val_inv_eq_inv_val]
  rw [this]
  exact hξc.inv₀ fun w => Units.ne_zero _

include hξc in
theorem measurable_term (Ψ' : AdelicGL2 (𝓞 K) K → ℂ) (hΨm : Measurable Ψ') (δ : GL (Fin 2) K) :
    Measurable (term K νZK ξK Ψ' δ) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := secondCountableTopology_gl K
  set F : AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ → ℂ := fun p =>
    (((ξK ⟨p.2, Subgroup.mem_top p.2⟩)⁻¹ : ℂˣ) : ℂ) *
      Ψ' (centralScalar (𝓞 K) K p.2 * (globalPoints (𝓞 K) K δ * p.1)) with hF
  have hFm : Measurable F := by
    refine ((continuous_xi_inv K ξK hξc).measurable.comp measurable_snd).mul (hΨm.comp ?_)
    exact (((continuous_centralScalar K).comp continuous_snd).mul
      (continuous_const.mul continuous_fst)).measurable
  have := hFm.stronglyMeasurable.integral_prod_right' (ν := νZK)
  exact this.measurable

include hξc in
theorem measurable_theta (Ψ' : AdelicGL2 (𝓞 K) K → ℂ) (hΨm : Measurable Ψ')
    (C : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) (hΨC : ∀ y ∉ C, Ψ' y = 0) :
    Measurable (theta K νZK ξK Ψ') := by
  haveI := countable_quot K
  have hT : ∀ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
      Measurable (term K νZK ξK Ψ' q.out) := fun q => measurable_term K νZK ξK hξc Ψ' hΨm q.out
  have hfin : ∀ g : AdelicGL2 (𝓞 K) K, (Function.support fun q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K) =>
      term K νZK ξK Ψ' q.out g).Finite := by
    intro g

    have hQfin := AutomorphicForm.finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact
      K C {1} {g} hC isCompact_singleton isCompact_singleton
    refine hQfin.subset fun q hq => ?_
    rw [Function.mem_support] at hq
    by_contra hqQ
    apply hq
    simp only [term]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun w => ?_)
    have : Ψ' (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g)) = 0 := by
      by_contra hne
      refine hqQ ⟨1, rfl, g, rfl, w, ?_⟩
      rw [inv_one, one_mul, ← mul_assoc, ← centralScalar_comm, mul_assoc]
      by_contra h'; exact hne (hΨC _ h')
    simp [this]
  have h : Measurable fun g : AdelicGL2 (𝓞 K) K =>
      ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K), term K νZK ξK Ψ' q.out g :=
    measurable_finsum_of_countable _ hT hfin
  exact h

omit [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] [νZK.IsHaarMeasure] in
theorem nullMeasurableSet_of_restrict {X : Type*} [MeasurableSpace X] (m : Measure X) {s t : Set X}
    (ht : MeasurableSet t) (hst : s ⊆ t) (hs : NullMeasurableSet s (m.restrict t)) : NullMeasurableSet s m := by
  obtain ⟨s', hsub, hs'm, hs'ae⟩ := hs.exists_measurable_superset_ae_eq
  have h1 : (m.restrict t) (s' \ s) = 0 := (ae_eq_set.1 hs'ae).1
  rw [Measure.restrict_apply' ht] at h1
  have hae : s =ᵐ[m] (s' ∩ t : Set X) := by
    rw [ae_eq_set]
    constructor
    · have : s \ (s' ∩ t) = ∅ := Set.diff_eq_empty.2 fun y hy => ⟨hsub hy, hst hy⟩
      rw [this, measure_empty]
    · refine measure_mono_null ?_ h1
      intro y hy; exact ⟨⟨hy.1.1, hy.2⟩, hy.1.2⟩
  exact (hs'm.inter ht).nullMeasurableSet.congr hae.symm

omit [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] [νZK.IsHaarMeasure] in
theorem nullMeasurableSet_canonicalTruncationDomain (α β : ℝ) :
    NullMeasurableSet (canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  by_cases h : ∃ d, IsTruncationDatum K α β d
  · have hspec := canonicalTruncationData_spec K h
    obtain ⟨-, -, -, hsub, hFD⟩ := hspec
    have hslab : MeasurableSet {g : AdelicGL2 (𝓞 K) K |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :=
      NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K α β
    exact nullMeasurableSet_of_restrict (adelicGLHaar (Fin 2) (𝓞 K) K) hslab hsub hFD.nullMeasurableSet
  · have : canonicalTruncationDomain K α β = ∅ := by
      show (canonicalTruncationData K α β).2.2 = ∅
      unfold canonicalTruncationData
      rw [dif_neg h]
    rw [this]
    exact MeasurableSet.empty.nullMeasurableSet

omit [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] [νZK.IsHaarMeasure] in

theorem measure_canonicalTruncationDomain_lt_top (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    adelicGLHaar (Fin 2) (𝓞 K) K (canonicalTruncationDomain K α β) < ⊤ := by
  by_cases h : ∃ d, IsTruncationDatum K α β d
  · have hspec := canonicalTruncationData_spec K h
    obtain ⟨-, -, -, hsub, hFD⟩ := hspec
    have := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K α β hα hαβ (canonicalTruncationDomain K α β) hFD
    exact lt_of_le_of_lt (measure_mono (Set.subset_inter Set.Subset.rfl hsub)) this
  · have : canonicalTruncationDomain K α β = ∅ := by
      show (canonicalTruncationData K α β).2.2 = ∅
      unfold canonicalTruncationData
      rw [dif_neg h]
    rw [this, measure_empty]
    exact ENNReal.zero_lt_top

theorem ae_ae_not_mem (N : Set (AdelicGL2 (𝓞 K) K)) (hNm : MeasurableSet N)
    (hN : adelicGLHaar (Fin 2) (𝓞 K) K N = 0) (δ : GL (Fin 2) K) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), ∀ᵐ w ∂νZK,
      centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K δ * g) ∉ N := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := secondCountableTopology_gl K
  haveI := isHaarMeasure_glHaar K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Sq : Set (AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ) :=
    {p | centralScalar (𝓞 K) K p.2 * (globalPoints (𝓞 K) K δ * p.1) ∈ N} with hSq
  have hSqm : MeasurableSet Sq :=
    hNm.preimage (((continuous_centralScalar K).comp continuous_snd).mul
      (continuous_const.mul continuous_fst)).measurable
  have hnull : (μ.prod νZK) Sq = 0 := by
    rw [Measure.prod_apply_symm hSqm]
    have : ∀ w : (AdeleRing (𝓞 K) K)ˣ, μ ((fun g => (g, w)) ⁻¹' Sq) = 0 := by
      intro w
      have : (fun g => (g, w)) ⁻¹' Sq =
          (fun g => (centralScalar (𝓞 K) K w * globalPoints (𝓞 K) K δ) * g) ⁻¹' N := by
        ext g; simp only [hSq, Set.mem_preimage, Set.mem_setOf_eq, mul_assoc]
      rw [this, measure_preimage_mul, hN]
    simp [this]
  exact Measure.ae_ae_of_ae_prod (measure_eq_zero_iff_ae_notMem.1 hnull)

theorem theta_ae_eq_of_forall_not_mem (Ψ₀ Ψ₁ : AdelicGL2 (𝓞 K) K → ℂ) (N : Set (AdelicGL2 (𝓞 K) K))
    (hNm : MeasurableSet N) (hN : adelicGLHaar (Fin 2) (𝓞 K) K N = 0) (hΨ : ∀ y ∉ N, Ψ₀ y = Ψ₁ y) :
    theta K νZK ξK Ψ₀ =ᵐ[adelicGLHaar (Fin 2) (𝓞 K) K] theta K νZK ξK Ψ₁ := by
  haveI := countable_quot K
  have hgood : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), ∀ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
      ∀ᵐ w ∂νZK, centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g) ∉ N :=
    ae_all_iff.2 fun q => ae_ae_not_mem K νZK N hNm hN q.out
  refine hgood.mono fun g hg => ?_
  simp only [theta]
  refine finsum_congr fun q => ?_
  simp only [term]
  refine integral_congr_ae ((hg q).mono fun w hw => ?_)
  dsimp only
  rw [hΨ _ hw]

end Fold

end

end ThetaAut19

open AutomorphicForm ThetaAut19 in

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨm : Measurable Ψ)
    (_hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0)
    (_hΨb : ∃ B : ℝ, ∀ y, ‖Ψ y‖ ≤ B) :
    letI := adeleBorel (𝓞 K) K
    IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK
      (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) := by
  classical
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := secondCountableTopology_gl K
  haveI := isHaarMeasure_glHaar K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ₀ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ₀
  obtain ⟨CΨ, hCΨ, hΨC⟩ := _hΨc
  obtain ⟨BΨ, hΨB⟩ := _hΨb

  set Ψ₀ := Φ₀.indicator Ψ with hΨ₀
  have hΨ₀C : ∀ y ∉ CΨ, Ψ₀ y = 0 := fun y hy => by
    simp only [hΨ₀, Set.indicator_apply_eq_zero]; exact fun _ => hΨC y hy
  have hΨ₀B : ∀ y, ‖Ψ₀ y‖ ≤ BΨ := fun y => (norm_indicator_le_norm_self _ _).trans (hΨB y)
  obtain ⟨Φ₁, -, hΦ₁m, hae⟩ := (nullMeasurableSet_canonicalTruncationDomain K α β).exists_measurable_superset_ae_eq
  rw [← hΦ₀] at hae
  set Ψ₁ := Φ₁.indicator Ψ with hΨ₁
  have hΨ₁m : Measurable Ψ₁ := _hΨm.indicator hΦ₁m
  have hΨ₁C : ∀ y ∉ CΨ, Ψ₁ y = 0 := fun y hy => by
    simp only [hΨ₁, Set.indicator_apply_eq_zero]; exact fun _ => hΨC y hy

  have hnull : μ ((Φ₁ \ Φ₀) ∪ (Φ₀ \ Φ₁)) = 0 := by
    have h := ae_eq_set.1 hae
    exact measure_union_null h.1 h.2
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hnull
  have hind : ∀ y ∉ N, Ψ₀ y = Ψ₁ y := by
    intro y hy
    have h1' : y ∈ Φ₀ → y ∈ Φ₁ := fun h => by
      by_contra h'; exact hy (hNsub (Or.inr ⟨h, h'⟩))
    have h2' : y ∈ Φ₁ → y ∈ Φ₀ := fun h => by
      by_contra h'; exact hy (hNsub (Or.inl ⟨h, h'⟩))
    simp only [hΨ₀, hΨ₁, Set.indicator_apply]
    by_cases h1 : y ∈ Φ₀
    · rw [if_pos h1, if_pos (h1' h1)]
    · rw [if_neg h1, if_neg (fun h => h1 (h2' h))]

  change IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK (theta K νZK ξK Ψ₀)
  refine (lsXiMemberAt_iff (𝓞 K) K μ ⊤ ξK Φ₀ (theta K νZK ξK Ψ₀)).2 ⟨?_, ?_⟩
  · exact isLsXiFunction_theta K νZK ξK hξt Ψ₀
  ·
    have hfin : μ Φ₀ < ⊤ := measure_canonicalTruncationDomain_lt_top K α β hα hαβ
    haveI : IsFiniteMeasure (μ.restrict Φ₀) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
    obtain ⟨M, hM⟩ := theta_bounded K νZK ξK hξt hξu Ψ₀ CΨ hCΨ hΨ₀C BΨ hΨ₀B
    have hmeas : AEStronglyMeasurable (theta K νZK ξK Ψ₀) (μ.restrict Φ₀) := by
      have h1 : Measurable (theta K νZK ξK Ψ₁) := measurable_theta K νZK ξK hξc Ψ₁ hΨ₁m CΨ hCΨ hΨ₁C
      have h2 := theta_ae_eq_of_forall_not_mem K νZK ξK Ψ₀ Ψ₁ N hNm hN0 hind
      exact (h1.aestronglyMeasurable.congr h2.symm).restrict
    exact MemLp.of_bound hmeas M (Filter.Eventually.of_forall hM)

end S_AutomorphicForm_isAutomorphicFnAt_finsum_integral_indicator_canonicalTruncationDomain
end P2MW
export P2MW.S_AutomorphicForm_isAutomorphicFnAt_finsum_integral_indicator_canonicalTruncationDomain (solution)
