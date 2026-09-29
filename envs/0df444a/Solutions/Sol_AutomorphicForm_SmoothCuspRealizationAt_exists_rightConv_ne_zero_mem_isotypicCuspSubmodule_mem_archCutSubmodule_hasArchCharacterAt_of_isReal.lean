-- Prove2me | solution 1 for AutomorphicForm.SmoothCuspRealizationAt.exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b44ba877-f7c4-5d06-b89d-97b7eaa8d0b5

import Mathlib
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

section ModShells

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume NumberField.AdelicVolume
open scoped ENNReal

namespace SmwShell

variable (F : Type) [Field F] [NumberField F]

private theorem memLp_two_restrict_of_bound (D : Set (AdelicGL2 (𝓞 F) F))
    (hD : adelicGLHaar (Fin 2) (𝓞 F) F D < ⊤)
    (v : AdelicGL2 (𝓞 F) F → ℂ) (hv : Continuous v) (C : ℝ) (hC : ∀ g ∈ D, ‖v g‖ ≤ C) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hD⟩
  refine MemLp.of_bound hv.aestronglyMeasurable C ?_
  rw [ae_restrict_iff (isClosed_le hv.norm continuous_const).measurableSet]
  exact ae_of_all _ hC

private theorem rightConv_mul_left_of_forall {φ f : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F}
    (hφ : ∀ x, φ (h * x) = φ x) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (h * g) = rightConv F φ f g := by
  rw [← rightConv_comp_mul_left]
  simp only [hφ]

private theorem rightConv_mul_left_of_forall_mul {φ f : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F}
    {c : ℂ} (hφ : ∀ x, φ (h * x) = c * φ x) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (h * g) = c * rightConv F φ f g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  rw [← rightConv_comp_mul_left, rightConv_apply, rightConv_apply]
  simp only [hφ, mul_assoc]
  exact MeasureTheory.integral_const_mul _ _

private theorem isLsXiFunction_rightConv_of_isLsXiFunction (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    IsLsXiFunction (𝓞 F) F Z ξ (rightConv F φ f) where
  left_invariant γ g := rightConv_mul_left_of_forall F (fun x => hφ.left_invariant γ x) g
  central_transform z g := rightConv_mul_left_of_forall_mul F (fun x => hφ.central_transform z x) g

private theorem memLp_rightConv_of_lt (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F
      ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))) ξ φ)
    (hφc : Continuous φ) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp (rightConv F φ f) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
  have hcont : Continuous (rightConv F φ f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hφc f hf).1
  obtain ⟨C, hC⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
      F c u d₁ d₂ T hc hd₁ hd hcov ξ f hf
  have hbound := hC φ hφ hφc
  have hfin : adelicGLHaar (Fin 2) (𝓞 F) F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) < ⊤ := by
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    exact measure_biUnion_lt_top T.finite_toSet
      (fun x _ => adelicGLHaar_mul_right_centreCutSiegelSet_lt_top F hc u hd₁ d₂ x)
  exact memLp_two_restrict_of_bound F _ hfin (rightConv F φ f) hcont _ hbound

end SmwShell

end ModShells

section ModConvHalf

set_option autoImplicit false

namespace ArchFiniteVector
namespace ConvHalf

variable (F : Type) [Field F] [NumberField F]

private theorem isFactorizableTestFn_mk (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) :
    IsFactorizableTestFn F (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) :=
  ⟨fa, ff, hfa, hff, fun _ => rfl⟩

end ArchFiniteVector.ConvHalf

end ModConvHalf

section ModKFinite

set_option autoImplicit false

open NumberField NumberField.AdelicHaar MeasureTheory
open AutomorphicForm

namespace ArchFiniteVector
namespace KFinite

variable (F : Type) [Field F] [NumberField F]

private theorem rightConv_mul_right (φ f : AdelicGL2 (𝓞 F) F → ℂ) (k g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (g * k) = rightConv F φ (fun y => f (k⁻¹ * y)) g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  rw [rightConv_apply, rightConv_apply]
  have key : (fun x => φ (g * k * x) * f x) =
      fun x => (fun y => φ (g * y) * f (k⁻¹ * y)) (k * x) := by
    funext x
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [key]
  exact MeasureTheory.integral_mul_left_eq_self (fun y => φ (g * y) * f (k⁻¹ * y)) k

private theorem integrable_rightConv_integrand (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (g : AdelicGL2 (𝓞 F) F) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    Integrable (fun x => φ (g * x) * f x) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hcont : Continuous fun x => φ (g * x) * f x := (hφ.comp (continuous_const_mul g)).mul hf
  have hsupp : HasCompactSupport fun x => φ (g * x) * f x := hfc.mul_left
  exact hcont.integrable_of_hasCompactSupport hsupp

private theorem rightConv_mem_span {n : ℕ} (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fs : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (hfs : ∀ i, Continuous (fs i)) (hfsc : ∀ i, HasCompactSupport (fs i))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range fs)) :
    rightConv F φ f ∈ Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i)) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  refine (Submodule.span_induction
    (p := fun f _ => (∀ g, Integrable (fun x => φ (g * x) * f x) (adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
      rightConv F φ f ∈ Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i)))
    ?_ ?_ ?_ ?_ hf).2
  · rintro _ ⟨i, rfl⟩
    exact ⟨fun g => integrable_rightConv_integrand F φ hφ (fs i) (hfs i) (hfsc i) g,
      Submodule.subset_span ⟨i, rfl⟩⟩
  · refine ⟨fun g => ?_, ?_⟩
    · have e : (fun x => φ (g * x) * (0 : AdelicGL2 (𝓞 F) F → ℂ) x) = fun _ => (0 : ℂ) := by
        funext x
        simp
      rw [e]
      exact integrable_zero _ _ _
    · have e : rightConv F φ (0 : AdelicGL2 (𝓞 F) F → ℂ) = 0 := by
        funext g
        simp [rightConv]
      rw [e]
      exact Submodule.zero_mem _
  · rintro f₁ f₂ - - ⟨h₁, m₁⟩ ⟨h₂, m₂⟩
    refine ⟨fun g => ?_, ?_⟩
    · have e : (fun x => φ (g * x) * (f₁ + f₂) x) = fun x => φ (g * x) * f₁ x + φ (g * x) * f₂ x := by
        funext x
        simp only [Pi.add_apply, mul_add]
      rw [e]
      exact (h₁ g).add (h₂ g)
    · have e : rightConv F φ (f₁ + f₂) = rightConv F φ f₁ + rightConv F φ f₂ := by
        funext g
        rw [Pi.add_apply, rightConv_apply, rightConv_apply, rightConv_apply]
        simp only [Pi.add_apply, mul_add]
        exact MeasureTheory.integral_add (h₁ g) (h₂ g)
      rw [e]
      exact Submodule.add_mem _ m₁ m₂
  · rintro a f₁ - ⟨h₁, m₁⟩
    refine ⟨fun g => ?_, ?_⟩
    · have e : (fun x => φ (g * x) * (a • f₁) x) = fun x => a * (φ (g * x) * f₁ x) := by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact (h₁ g).const_mul a
    · have e : rightConv F φ (a • f₁) = a • rightConv F φ f₁ := by
        funext g
        rw [Pi.smul_apply, smul_eq_mul, rightConv_apply, rightConv_apply, ← MeasureTheory.integral_const_mul]
        congr 1
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact Submodule.smul_mem _ a m₁

private theorem exists_finiteDimensional_mem_of_forall_mem_span {n : ℕ} {H : Type} [Monoid H]
    (ι : H →* AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fs : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (hfs : ∀ i, Continuous (fs i)) (hfsc : ∀ i, HasCompactSupport (fs i))
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hW : ∀ k : H, (fun y => f ((ι k)⁻¹ * y)) ∈ Submodule.span ℂ (Set.range fs)) :
    ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ V ∧ rightConv F φ f ∈ V ∧
      ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V := by
  refine ⟨Submodule.span ℂ (Set.range fun k : H => fun x => rightConv F φ f (x * ι k)), ?_, ?_, ?_⟩
  · have hle : Submodule.span ℂ (Set.range fun k : H => fun x => rightConv F φ f (x * ι k)) ≤
        Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i)) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      show (fun x => rightConv F φ f (x * ι k)) ∈ Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i))
      have e : (fun x => rightConv F φ f (x * ι k)) = rightConv F φ (fun y => f ((ι k)⁻¹ * y)) := by
        funext x
        exact rightConv_mul_right F φ f (ι k) x
      rw [e]
      exact rightConv_mem_span F φ hφ fs hfs hfsc _ (hW k)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i))) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    exact Submodule.finiteDimensional_of_le hle
  · have e : (fun x => rightConv F φ f (x * ι 1)) = rightConv F φ f := by
      funext x
      rw [map_one, mul_one]
    have h1 : (fun x => rightConv F φ f (x * ι 1)) ∈
        Submodule.span ℂ (Set.range fun k : H => fun x => rightConv F φ f (x * ι k)) :=
      Submodule.subset_span ⟨1, rfl⟩
    rwa [e] at h1
  · intro k v hv
    refine Submodule.span_induction
      (p := fun v _ => (fun x => v (x * ι k)) ∈
        Submodule.span ℂ (Set.range fun k : H => fun x => rightConv F φ f (x * ι k)))
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      funext x
      simp only [map_mul, mul_assoc]
    · exact Submodule.zero_mem _
    · exact fun _ _ _ _ hu hw => Submodule.add_mem _ hu hw
    · exact fun c _ _ hu => Submodule.smul_mem _ c hu

end ArchFiniteVector.KFinite

end ModKFinite

section ModArchCut

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

namespace ArchFiniteVector
namespace ArchCut

section Generic

variable {H G : Type*} [Group H] [Group G]

private def translateOn (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) (k : H) : V →ₗ[ℂ] V where
  toFun v := ⟨fun x => (v : G → ℂ) (x * ι k), hV k v v.2⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)

private theorem translateOn_apply_coe (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) (k : H) (v : V) (x : G) :
    (translateOn ι V hV k v : G → ℂ) x = (v : G → ℂ) (x * ι k) :=
  rfl

private theorem translateOn_one (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) :
    translateOn ι V hV 1 = LinearMap.id :=
  LinearMap.ext fun v => Subtype.ext (funext fun x => by simp [translateOn_apply_coe])

private theorem translateOn_mul (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) (k₁ k₂ : H) :
    translateOn ι V hV (k₁ * k₂) = translateOn ι V hV k₁ ∘ₗ translateOn ι V hV k₂ :=
  LinearMap.ext fun v => Subtype.ext (funext fun x => by simp [translateOn_apply_coe, mul_assoc])

private def transportRep (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) {n : ℕ} (e : V ≃ₗ[ℂ] (Fin n → ℂ)) :
    Representation ℂ H (Fin n → ℂ) where
  toFun k := (e : V →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ translateOn ι V hV k ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] V)
  map_one' := LinearMap.ext fun a => by simp [translateOn_one]
  map_mul' k₁ k₂ := LinearMap.ext fun a => by simp [translateOn_mul, Module.End.mul_apply]

private theorem transportRep_apply (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) {n : ℕ} (e : V ≃ₗ[ℂ] (Fin n → ℂ)) (k : H)
    (a : Fin n → ℂ) : transportRep ι V hV e k a = e (translateOn ι V hV k (e.symm a)) :=
  rfl

private theorem isRightEquivariant_subtype_comp_symm (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) {n : ℕ} (e : V ≃ₗ[ℂ] (Fin n → ℂ)) :
    IsRightEquivariant ι (transportRep ι V hV e)
      (V.subtype ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] V)) := by
  intro k a x
  simp [transportRep_apply, translateOn_apply_coe]

private theorem exists_rep_mem_typeSubmodule (ι : H →* G) {u : G → ℂ} (V : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ V] (hu : u ∈ V) (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) :
    ∃ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)), u ∈ typeSubmodule ι ρ := by
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  refine ⟨Module.finrank ℂ V, transportRep ι V hV e, ?_⟩
  have hmem := mem_typeSubmodule_of_isRightEquivariant (isRightEquivariant_subtype_comp_symm ι V hV e)
    (e ⟨u, hu⟩)
  simpa using hmem

private theorem comp_inv_mem_span {N : ℕ} (b : Fin N → G → ℂ) {h : G → ℂ}
    (hh : h ∈ Submodule.span ℂ (Set.range b)) :
    (fun x => h x⁻¹) ∈ Submodule.span ℂ (Set.range fun i => fun x => b i x⁻¹) := by
  refine Submodule.span_induction
    (p := fun h _ => (fun x => h x⁻¹) ∈ Submodule.span ℂ (Set.range fun i => fun x => b i x⁻¹))
    ?_ ?_ ?_ ?_ hh
  · rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · exact Submodule.zero_mem _
  · exact fun _ _ _ _ hu hw => Submodule.add_mem _ hu hw
  · exact fun c _ _ hu => Submodule.smul_mem _ c hu

private theorem exists_stable_of_translates_mem (ι : H →* G) (u : G → ℂ) (W : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ W] (hW : ∀ k : H, (fun x => u (x * ι k)) ∈ W) :
    ∃ V : Submodule ℂ (G → ℂ), FiniteDimensional ℂ V ∧ u ∈ V ∧
      ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V := by
  refine ⟨Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)), ?_, ?_, ?_⟩
  · have hle : Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)) ≤ W := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      exact hW k
    exact Submodule.finiteDimensional_of_le hle
  · have e : (fun x => u (x * ι 1)) = u := by
      funext x
      rw [map_one, mul_one]
    have h1 : (fun x => u (x * ι 1)) ∈ Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)) :=
      Submodule.subset_span ⟨1, rfl⟩
    rwa [e] at h1
  · intro k v hv
    refine Submodule.span_induction
      (p := fun v _ => (fun x => v (x * ι k)) ∈ Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)))
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      funext x
      simp only [map_mul, mul_assoc]
    · exact Submodule.zero_mem _
    · exact fun _ _ _ _ hu hw => Submodule.add_mem _ hu hw
    · exact fun c _ _ hu => Submodule.smul_mem _ c hu

private def dualCarrierEquiv (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ) :=
  (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun.symm

private def dualTransport {n : ℕ} (σ : Representation ℂ H (Fin n → ℂ)) : Representation ℂ H (Fin n → ℂ) where
  toFun k := ((dualCarrierEquiv n).symm : Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ σ.dual k ∘ₗ
    (dualCarrierEquiv n : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ))
  map_one' := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_one, Module.End.one_apply,
      LinearEquiv.symm_apply_apply]
  map_mul' k₁ k₂ := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_mul, Module.End.mul_apply,
      LinearEquiv.apply_symm_apply]

private theorem dualTransport_apply {n : ℕ} (σ : Representation ℂ H (Fin n → ℂ)) (k : H) (a : Fin n → ℂ) :
    dualTransport σ k a = (dualCarrierEquiv n).symm (σ.dual k (dualCarrierEquiv n a)) :=
  rfl

private def dualEquiv (n : ℕ) : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  ((dualCarrierEquiv n).symm.dualMap).trans (Module.evalEquiv ℂ (Fin n → ℂ)).symm

private theorem apply_dualEquiv (n : ℕ) (φ ψ : Module.Dual ℂ (Fin n → ℂ)) :
    ψ (dualEquiv n φ) = φ ((dualCarrierEquiv n).symm ψ) := by
  simp only [dualEquiv, LinearEquiv.trans_apply, Module.apply_evalEquiv_symm_apply, LinearEquiv.dualMap_apply]

private theorem dualEquiv_dual_apply {n : ℕ} (σ : Representation ℂ H (Fin n → ℂ)) (k : H)
    (φ : Module.Dual ℂ (Fin n → ℂ)) :
    dualEquiv n ((dualTransport σ).dual k φ) = σ k (dualEquiv n φ) := by
  have key : ∀ ψ : Module.Dual ℂ (Fin n → ℂ),
      ψ (dualEquiv n ((dualTransport σ).dual k φ)) = ψ (σ k (dualEquiv n φ)) := by
    intro ψ
    rw [apply_dualEquiv]
    change φ (dualTransport σ k⁻¹ ((dualCarrierEquiv n).symm ψ)) = _
    rw [dualTransport_apply, LinearEquiv.apply_symm_apply]
    change φ ((dualCarrierEquiv n).symm (ψ ∘ₗ σ k⁻¹⁻¹)) = _
    rw [inv_inv, ← apply_dualEquiv n φ (ψ ∘ₗ σ k)]
    rfl
  exact (Module.evalEquiv ℂ (Fin n → ℂ)).injective (LinearMap.ext fun ψ => by
    simpa only [Module.evalEquiv_apply, Module.Dual.eval_apply] using key ψ)

private theorem exists_rep_mem_typeSubmodule_dual (ι : H →* G) {u : G → ℂ} (V : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ V] (hu : u ∈ V) (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) :
    ∃ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)), u ∈ typeSubmodule ι ρ.dual := by
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  refine ⟨Module.finrank ℂ V, dualTransport (transportRep ι V hV e), ?_⟩
  have hT : IsRightEquivariant ι (dualTransport (transportRep ι V hV e)).dual
      ((V.subtype ∘ₗ (e.symm : (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] V)) ∘ₗ
        (dualEquiv (Module.finrank ℂ V) :
          Module.Dual ℂ (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ))) := by
    intro k φ x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, dualEquiv_dual_apply]
    exact isRightEquivariant_subtype_comp_symm ι V hV e k (dualEquiv _ φ) x
  have hmem := mem_typeSubmodule_of_isRightEquivariant hT ((dualEquiv (Module.finrank ℂ V)).symm (e ⟨u, hu⟩))
  simpa using hmem

end Generic

private theorem exists_archTypeFamily_mem_archCutSubmodule (F : Type) [Field F] [NumberField F]
    (u : AdelicGL2 (𝓞 F) F → ℂ)
    (hV : ∀ w : InfinitePlace F, ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ V ∧ u ∈ V ∧
        ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ v ∈ V, (fun x => v (x * rowIsometryInclAt₀ F w k)) ∈ V) :
    ∃ tys : ArchTypeFamily F, u ∈ archCutSubmodule F tys := by
  have h : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w, u ∈ archTypeSubmoduleAt F w τ := by
    intro w
    obtain ⟨V, hfin, hu, hstab⟩ := hV w
    haveI := hfin
    obtain ⟨n, ρ, hmem⟩ := exists_rep_mem_typeSubmodule (rowIsometryInclAt₀ F w) V hu hstab
    exact ⟨⟨n, ρ⟩, hmem⟩
  choose τ hτ using h
  refine ⟨⟨fun _ => 1, fun w _ => τ w⟩, ?_⟩
  rw [mem_archCutSubmodule_iff]
  intro w
  exact Submodule.mem_iSup_of_mem (0 : Fin 1) (hτ w)

end ArchFiniteVector.ArchCut

end ModArchCut

section SEPcore

open MeasureTheory

namespace Ws23
namespace SMinf
namespace Sep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def IsSep (L : ℝ → E →ₗ[ℝ] E) (u : E → ℝ) : Prop :=
  ∃ (m : ℕ) (s : Fin m → ℝ → ℝ) (g : Fin m → E → ℝ),
    (∀ k, Continuous (s k)) ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k)) ∧ ∀ θ M, u (L θ M) = ∑ k, s k θ * g k M

variable {L : ℝ → E →ₗ[ℝ] E}

omit [FiniteDimensional ℝ E] in
theorem IsSep.const (c : ℝ) : IsSep L (fun _ => c) :=
  ⟨1, fun _ _ => 1, fun _ _ => c, fun _ => continuous_const, fun _ => contDiff_const, fun θ M => by simp⟩

omit [FiniteDimensional ℝ E] in
theorem IsSep.add {u v : E → ℝ} (hu : IsSep L u) (hv : IsSep L v) : IsSep L (u + v) := by
  obtain ⟨m, s, g, hs, hg, h⟩ := hu
  obtain ⟨m', s', g', hs', hg', h'⟩ := hv
  refine ⟨m + m', Fin.append s s', Fin.append g g', ?_, ?_, fun θ M => ?_⟩
  · intro k; refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa only [Fin.append_left] using hs i
    · simpa only [Fin.append_right] using hs' j
  · intro k; refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa only [Fin.append_left] using hg i
    · simpa only [Fin.append_right] using hg' j
  · rw [Pi.add_apply, h, h', Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

omit [FiniteDimensional ℝ E] in
theorem IsSep.mul {u v : E → ℝ} (hu : IsSep L u) (hv : IsSep L v) : IsSep L (u * v) := by
  obtain ⟨m, s, g, hs, hg, h⟩ := hu
  obtain ⟨m', s', g', hs', hg', h'⟩ := hv
  refine ⟨m * m', fun k θ => s (finProdFinEquiv.symm k).1 θ * s' (finProdFinEquiv.symm k).2 θ,
    fun k M => g (finProdFinEquiv.symm k).1 M * g' (finProdFinEquiv.symm k).2 M,
    fun k => (hs _).mul (hs' _), fun k => (hg _).mul (hg' _), fun θ M => ?_⟩
  rw [Pi.mul_apply, h, h', Finset.sum_mul_sum, ← Finset.sum_product', ← finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl fun k _ => by ring

omit [FiniteDimensional ℝ E] in
theorem IsSep.smul {u : E → ℝ} (c : ℝ) (hu : IsSep L u) : IsSep L (c • u) := by
  have : c • u = (fun _ => c) * u := by funext x; simp
  rw [this]; exact (IsSep.const c).mul hu

theorem IsSep.linear (hL : ∀ v : E, Continuous fun θ => L θ v) (ℓ : E →ₗ[ℝ] ℝ) : IsSep L ℓ := by
  let b := Module.finBasis ℝ E
  refine ⟨Module.finrank ℝ E, fun j θ => ℓ (L θ (b j)), fun j M => b.coord j M,
    fun j => (ℓ.continuous_of_finiteDimensional).comp (hL (b j)),
    fun j => (LinearMap.toContinuousLinearMap (b.coord j)).contDiff, fun θ M => ?_⟩
  conv_lhs => rw [← b.sum_repr M]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_smul, smul_eq_mul, Module.Basis.coord_apply]
  ring

def polyAlg' (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Subalgebra ℝ (E → ℝ) :=
  Algebra.adjoin ℝ (Set.range fun ℓ : E →ₗ[ℝ] ℝ => (ℓ : E → ℝ))

theorem isSep_of_mem_polyAlg' (hL : ∀ v : E, Continuous fun θ => L θ v) {u : E → ℝ} (hu : u ∈ polyAlg' E) :
    IsSep L u := by
  refine Algebra.adjoin_induction (hx := hu) ?_ ?_ ?_ ?_
  · rintro _ ⟨ℓ, rfl⟩; exact IsSep.linear hL ℓ
  · intro c
    have : (algebraMap ℝ (E → ℝ) c) = fun _ => c := by funext x; simp
    rw [this]; exact IsSep.const c
  · intro u v _ _ hu hv; exact hu.add hv
  · intro u v _ _ hu hv; exact hu.mul hv

theorem IsSep.contDiff_average {u : E → ℝ} (hu : IsSep L u) (c : ℝ → ℂ) (hc : Continuous c) (a b : ℝ) :
    ∃ G : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧ ∀ M, (∫ θ in a..b, c θ * (u (L θ M) : ℂ)) = G M := by
  obtain ⟨m, s, g, hs, hg, h⟩ := hu
  refine ⟨fun M => ∑ k, (∫ θ in a..b, c θ * (s k θ : ℂ)) * (g k M : ℂ), ?_, fun M => ?_⟩
  · refine ContDiff.sum fun k _ => contDiff_const.mul ?_
    exact Complex.ofRealCLM.contDiff.comp (hg k)
  · simp_rw [h, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [← intervalIntegral.integral_mul_const]
      refine intervalIntegral.integral_congr fun θ _ => by ring
    · intro k _
      exact (hc.mul ((Complex.continuous_ofReal.comp (hs k)).mul continuous_const)).intervalIntegrable
        (μ := MeasureTheory.volume) _ _

theorem span_image_of_addOn {X : Type*} [TopologicalSpace X] {N : ℕ} (b : Fin N → X → ℂ)
    (hb : ∀ i, Continuous (b i)) (T : (X → ℂ) → (X → ℂ))
    (hadd : ∀ u v : X → ℂ, Continuous u → Continuous v → T (u + v) = T u + T v)
    (hsmul : ∀ (c : ℂ) (u : X → ℂ), T (c • u) = c • T u) {u : X → ℂ}
    (hu : u ∈ Submodule.span ℂ (Set.range b)) :
    T u ∈ Submodule.span ℂ (Set.range fun i => T (b i)) := by
  suffices h : Continuous u ∧ T u ∈ Submodule.span ℂ (Set.range fun i => T (b i)) from h.2
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨i, rfl⟩
    exact ⟨hb i, Submodule.subset_span ⟨i, rfl⟩⟩
  · refine ⟨continuous_zero, ?_⟩
    have h0 : T 0 = 0 := by simpa using hsmul 0 0
    rw [h0]
    exact Submodule.zero_mem _
  · intro u v _ _ hu hv
    exact ⟨hu.1.add hv.1, by rw [hadd u v hu.1 hv.1]; exact Submodule.add_mem _ hu.2 hv.2⟩
  · intro c u _ hu
    exact ⟨hu.1.const_smul c, by rw [hsmul]; exact Submodule.smul_mem _ c hu.2⟩

end Ws23.SMinf.Sep

end SEPcore

section ROT5

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open scoped Classical

noncomputable section

namespace Ws23
namespace SMinf
namespace Rot

def rotMat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

theorem det_rotMat (θ : ℝ) : (rotMat θ).det = 1 := by
  have h : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    rw [← sq, ← sq]; exact Real.cos_sq_add_sin_sq θ
  simp [rotMat, Matrix.det_fin_two]
  linarith

def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotMat θ) (by rw [det_rotMat]; exact one_ne_zero)

theorem rotGL_coe (θ : ℝ) : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat θ := rfl

theorem rotGL_mem (θ : ℝ) : rotGL θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨det_rotMat θ, ?_, ?_⟩
  · rw [rotGL_coe, det_rotMat, norm_one]
  · intro x y
    have h00 : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = Real.cos θ := rfl
    have h01 : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = Real.sin θ := rfl
    have h10 : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -Real.sin θ := rfl
    have h11 : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = Real.cos θ := rfl
    rw [h00, h01, h10, h11, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, sq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq θ

def rotSO (θ : ℝ) : rowIsometrySubgroup₀ ℝ := ⟨rotGL θ, rotGL_mem θ⟩

theorem archWeightOneℝ_rotSO (θ : ℝ) :
    ((archWeightOneℝ (rotSO θ) : ℂˣ) : ℂ) = ⟨Real.cos θ, Real.sin θ⟩ := rfl

theorem archWeightOneℝ_rotSO_eq_exp (θ : ℝ) :
    ((archWeightOneℝ (rotSO θ) : ℂˣ) : ℂ) = Complex.exp (θ * Complex.I) := by
  rw [archWeightOneℝ_rotSO, Complex.exp_mul_I]
  apply Complex.ext <;>
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im]

theorem archWeightCharℝ_rotSO_eq_exp (k : ℤ) (θ : ℝ) :
    ((archWeightCharℝ k (rotSO θ) : ℂˣ) : ℂ) = Complex.exp (Complex.I * k * θ) := by
  rw [archWeightCharℝ, MonoidHom.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val,
    archWeightOneℝ_rotSO_eq_exp, ← Complex.exp_int_mul]
  congr 1
  ring

theorem rotSO_add (θ θ' : ℝ) : rotSO (θ + θ') = rotSO θ * rotSO θ' := by
  apply Subtype.ext
  apply Units.ext
  show rotMat (θ + θ') = rotMat θ * rotMat θ'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem rotSO_zero : rotSO 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show rotMat 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat]

theorem rotSO_periodic : Function.Periodic rotSO (2 * Real.pi) := by
  intro θ
  apply Subtype.ext
  apply Units.ext
  show rotMat (θ + 2 * Real.pi) = rotMat θ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat]

theorem exists_rotSO_eq (k : rowIsometrySubgroup₀ ℝ) : ∃ θ : ℝ, rotSO θ = k := by
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ k.2
  set a := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set z : ℂ := ⟨a, b⟩ with hz
  have hz1 : ‖z‖ = 1 := by
    have : Complex.normSq z = 1 := by rw [Complex.normSq_mk]; nlinarith [hab]
    rw [Complex.norm_def, this, Real.sqrt_one]
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; exact zero_ne_one hz1
  refine ⟨Complex.arg z, ?_⟩
  have hcos : Real.cos (Complex.arg z) = a := by
    rw [Complex.cos_arg hz0, hz1, div_one]
  have hsin : Real.sin (Complex.arg z) = b := by
    rw [Complex.sin_arg, hz1, div_one]
  apply Subtype.ext
  apply Units.ext
  show rotMat (Complex.arg z) = ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [rotMat] using hcos
  · simpa [rotMat] using hsin
  · simp [rotMat, hsin]; exact h10.symm
  · simp [rotMat, hcos]; exact h11.symm

section Transport

variable (F : Type) [Field F] [NumberField F]

def rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm he (rotSO θ)

omit [NumberField F] in
theorem norm_symm_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  have := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

variable {F}

omit [NumberField F] in
theorem rowIsometrySubgroup₀Map_rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      (rotAt F hw he θ) = rotSO θ := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (ringEquivRealOfIsReal hw) ((ringEquivRealOfIsReal hw).symm (rotMat θ i j)) = rotMat θ i j
  exact RingEquiv.apply_symm_apply _ _

omit [NumberField F] in

theorem map_rotGL_eq_rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom (rotGL θ) =
      ((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) := by
  apply Units.ext
  ext i j
  rfl

omit [NumberField F] in
theorem rotAt_coe_apply {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) (i j : Fin 2) :
    (((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) i j = (ringEquivRealOfIsReal hw).symm (rotMat θ i j) := rfl

omit [NumberField F] in
theorem rotAt_add {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ θ' : ℝ) :
    rotAt F hw he (θ + θ') = rotAt F hw he θ * rotAt F hw he θ' := by
  unfold rotAt; rw [rotSO_add, map_mul]

omit [NumberField F] in
theorem rotAt_zero {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) : rotAt F hw he 0 = 1 := by
  unfold rotAt; rw [rotSO_zero, map_one]

omit [NumberField F] in
theorem rotAt_periodic {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) :
    Function.Periodic (rotAt F hw he) (2 * Real.pi) := fun θ => by
  unfold rotAt; rw [rotSO_periodic]

omit [NumberField F] in

theorem exists_rotAt_eq {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (k : rowIsometrySubgroup₀ w.Completion) :
    ∃ θ : ℝ, rotAt F hw he θ = k := by
  obtain ⟨θ, hθ⟩ := exists_rotSO_eq
    (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) k)
  refine ⟨θ, ?_⟩
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [rotAt_coe_apply]
  have hij : rotMat θ i j =
      (ringEquivRealOfIsReal hw) (((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) := by
    have := congrArg (fun m : rowIsometrySubgroup₀ ℝ =>
      ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) hθ
    exact this
  rw [hij, RingEquiv.symm_apply_apply]

end Transport

section Adelic

variable {F : Type} [Field F] [NumberField F]

theorem adelicArchGLInclAt_coe_apply (w : InfinitePlace F) (kk : GL (Fin 2) w.Completion) (i j : Fin 2) :
    ((adelicArchGLInclAt F w kk : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      ((fun v : InfinitePlace F =>
          (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w
            (kk : Matrix (Fin 2) (Fin 2) w.Completion) v) i j : InfiniteAdeleRing F),
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) :=
  rfl

def archRot (w : InfinitePlace F) (hw : w.IsReal) (θ : ℝ) : AdelicGL2 (𝓞 F) F :=
  adelicArchGLInclAt F w
    ((rotAt F hw (norm_symm_ringEquivRealOfIsReal F hw) θ : rowIsometrySubgroup₀ w.Completion) :
      GL (Fin 2) w.Completion)

theorem archRot_add (w : InfinitePlace F) (hw : w.IsReal) (θ θ' : ℝ) :
    archRot w hw (θ + θ') = archRot w hw θ * archRot w hw θ' := by
  unfold archRot; rw [rotAt_add, Subgroup.coe_mul, map_mul]

theorem archRot_zero (w : InfinitePlace F) (hw : w.IsReal) : archRot w hw 0 = 1 := by
  unfold archRot; rw [rotAt_zero, Subgroup.coe_one, map_one]

theorem archRot_periodic (w : InfinitePlace F) (hw : w.IsReal) :
    Function.Periodic (archRot w hw) (2 * Real.pi) := fun θ => by
  unfold archRot; rw [rotAt_periodic]

theorem archRot_neg_mul (w : InfinitePlace F) (hw : w.IsReal) (θ : ℝ) :
    archRot w hw (-θ) * archRot w hw θ = 1 := by
  rw [← archRot_add, neg_add_cancel, archRot_zero]

theorem archRot_inv (w : InfinitePlace F) (hw : w.IsReal) (θ : ℝ) :
    (archRot w hw θ)⁻¹ = archRot w hw (-θ) :=
  inv_eq_of_mul_eq_one_left (archRot_neg_mul w hw θ)

theorem glFin_archRot (w : InfinitePlace F) (hw : w.IsReal) (θ : ℝ) :
    glFin (𝓞 F) F (archRot w hw θ) = 1 := by
  apply Units.ext; ext i j; rfl

theorem continuous_rotMat_apply (i j : Fin 2) : Continuous fun θ : ℝ => rotMat θ i j := by
  fin_cases i <;> fin_cases j
  · exact Real.continuous_cos
  · exact Real.continuous_sin
  · exact Real.continuous_sin.neg
  · exact Real.continuous_cos

omit [NumberField F] in
theorem continuous_symm_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) :
    Continuous (ringEquivRealOfIsReal hw).symm := by
  have hiso : Isometry ((ringEquivRealOfIsReal hw).symm.toRingHom.toAddMonoidHom) :=
    AddMonoidHomClass.isometry_of_norm _ (norm_symm_ringEquivRealOfIsReal F hw)
  exact hiso.continuous

theorem continuous_archRot_val (w : InfinitePlace F) (hw : w.IsReal) :
    Continuous fun θ : ℝ =>
      ((archRot w hw θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [archRot, adelicArchGLInclAt_coe_apply]
  refine Continuous.prodMk ?_ continuous_const
  refine continuous_pi fun v => ?_
  by_cases hv : v = w
  · subst hv
    simp only [Function.update_self]
    show Continuous fun θ : ℝ =>
      (((rotAt F hw (norm_symm_ringEquivRealOfIsReal F hw) θ : rowIsometrySubgroup₀ v.Completion) :
        GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i j
    simp only [rotAt_coe_apply]
    exact (continuous_symm_ringEquivRealOfIsReal hw).comp (continuous_rotMat_apply i j)
  · simp only [Function.update_of_ne hv]
    exact continuous_const

theorem continuous_archRot (w : InfinitePlace F) (hw : w.IsReal) :
    Continuous fun θ : ℝ => (archRot w hw θ : AdelicGL2 (𝓞 F) F) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_archRot_val w hw, ?_⟩
  have : (fun θ : ℝ => ((archRot w hw θ)⁻¹ : AdelicGL2 (𝓞 F) F).val) =
      fun θ => (archRot w hw (-θ) : AdelicGL2 (𝓞 F) F).val := by
    funext θ; rw [archRot_inv]
  show Continuous fun θ : ℝ => ((archRot w hw θ)⁻¹ : AdelicGL2 (𝓞 F) F).val
  rw [this]
  exact (continuous_archRot_val w hw).comp continuous_neg

theorem det_archRot (w : InfinitePlace F) (hw : w.IsReal) (θ : ℝ) :
    Matrix.GeneralLinearGroup.det (archRot w hw θ) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_fin_two]
  simp only [archRot, adelicArchGLInclAt_coe_apply]
  refine Prod.ext ?_ ?_
  · show (fun v : InfinitePlace F => _) = (1 : InfiniteAdeleRing F)
    funext v
    show (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w _ v) 0 0 *
        (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w _ v) 1 1 -
      (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w _ v) 0 1 *
        (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w _ v) 1 0 = 1
    by_cases hv : v = w
    · subst hv
      simp only [Function.update_self, rotAt_coe_apply, ← map_mul, ← map_sub]
      rw [← (ringEquivRealOfIsReal hw).symm.map_one]
      congr 1
      have := det_rotMat θ
      rw [Matrix.det_fin_two] at this
      exact this
    · simp [Function.update_of_ne hv]
  · show (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) 0 0 *
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) 1 1 -
      (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) 0 1 *
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) 1 0 =
      (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    simp

end Adelic

section Commute

variable {F : Type} [Field F] [NumberField F]

theorem glArch_adelicArchGLInclAt (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    glFin (𝓞 F) F (adelicArchGLInclAt F w k) = 1 := by
  apply Units.ext; ext i j; rfl

theorem AdeleRing.fst_add (a b : AdeleRing (𝓞 F) F) : (a + b).1 = a.1 + b.1 := rfl
theorem AdeleRing.fst_mul (a b : AdeleRing (𝓞 F) F) : (a * b).1 = a.1 * b.1 := rfl
theorem AdeleRing.snd_add (a b : AdeleRing (𝓞 F) F) : (a + b).2 = a.2 + b.2 := rfl
theorem AdeleRing.snd_mul (a b : AdeleRing (𝓞 F) F) : (a * b).2 = a.2 * b.2 := rfl

theorem commute_of_glArch_eq_one_of_glFin_eq_one {a b : AdelicGL2 (𝓞 F) F}
    (ha : glArch (𝓞 F) F a = 1) (hb : glFin (𝓞 F) F b = 1) : a * b = b * a := by
  have ha' : ∀ i j : Fin 2, ((a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j := fun i j => by
    have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) ha
    exact this
  have hb' : ∀ i j : Fin 2, ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 =
      (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j := fun i j => by
    have := congrArg (fun m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
      (m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) hb
    exact this
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  all_goals obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  all_goals
    refine Prod.ext ?_ ?_
    · rw [AdeleRing.fst_add, AdeleRing.fst_add, AdeleRing.fst_mul, AdeleRing.fst_mul,
        AdeleRing.fst_mul, AdeleRing.fst_mul]
      simp only [ha']
      simp
    · rw [AdeleRing.snd_add, AdeleRing.snd_add, AdeleRing.snd_mul, AdeleRing.snd_mul,
        AdeleRing.snd_mul, AdeleRing.snd_mul]
      simp only [hb']
      simp

theorem glArch_eq_one_of_mem_finiteAdelicGL2Subgroup {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ finiteAdelicGL2Subgroup F) : glArch (𝓞 F) F u = 1 := hu

theorem heckeGen_mem_finiteAdelicGL2Subgroup (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    heckeGen (𝓞 F) F v ∈ finiteAdelicGL2Subgroup F := by
  show glArch (𝓞 F) F (heckeGen (𝓞 F) F v) = 1
  apply Units.ext
  rw [Units.val_one]
  ext i j
  rw [glArch_apply]
  unfold heckeGen
  exact heckeGenAt_fst (uniformizerUnit F v) i j

end Commute

section FourierAverage

variable {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)

def Pn (n : ℤ) (ψ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(Complex.I * n * θ)) * ψ (g * archRot w hw θ)

theorem Pn_apply (n : ℤ) (ψ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    Pn w hw n ψ g =
      ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(Complex.I * n * θ)) * ψ (g * archRot w hw θ) := rfl

theorem continuous_expChar (n : ℤ) : Continuous fun θ : ℝ => Complex.exp (-(Complex.I * n * θ)) := by
  fun_prop

theorem expChar_periodic (n : ℤ) :
    Function.Periodic (fun θ : ℝ => Complex.exp (-(Complex.I * n * θ))) (2 * Real.pi) := by
  intro θ
  simp only
  have : -(Complex.I * n * ((θ + 2 * Real.pi : ℝ) : ℂ)) = -(Complex.I * n * θ) + (-n : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

variable {w hw}

theorem hasArchCharacterAt₀_Pn (n : ℤ) (ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    HasArchCharacterAt₀ F w
      ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) (Pn w hw n ψ) := by
  intro k g
  obtain ⟨α, rfl⟩ := exists_rotAt_eq hw (norm_symm_ringEquivRealOfIsReal F hw) k
  rw [MonoidHom.comp_apply, rowIsometrySubgroup₀Map_rotAt, archWeightCharℝ_rotSO_eq_exp]
  show Pn w hw n ψ (g * archRot w hw α) = _
  rw [Pn_apply, Pn_apply]
  have hP : Function.Periodic
      (fun θ : ℝ => Complex.exp (-(Complex.I * n * θ)) * ψ (g * archRot w hw θ)) (2 * Real.pi) := by
    intro θ
    have h1 := expChar_periodic n θ
    simp only at h1 ⊢
    rw [h1, archRot_periodic]
  calc (∫ θ in (0 : ℝ)..2 * Real.pi,
          Complex.exp (-(Complex.I * n * θ)) * ψ (g * archRot w hw α * archRot w hw θ))
      = ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (Complex.I * n * α) *
          (fun t : ℝ => Complex.exp (-(Complex.I * n * t)) * ψ (g * archRot w hw t)) (α + θ) := by
        apply intervalIntegral.integral_congr
        intro θ _
        simp only [mul_assoc, ← archRot_add]
        rw [← mul_assoc (Complex.exp _), ← Complex.exp_add]
        congr 2
        push_cast; ring
    _ = Complex.exp (Complex.I * n * α) *
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            (fun t : ℝ => Complex.exp (-(Complex.I * n * t)) * ψ (g * archRot w hw t)) (α + θ) := by
        rw [intervalIntegral.integral_const_mul]
    _ = Complex.exp (Complex.I * n * α) *
          ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(Complex.I * n * θ)) * ψ (g * archRot w hw θ) := by
        congr 1
        rw [intervalIntegral.integral_comp_add_left
          (fun t : ℝ => Complex.exp (-(Complex.I * n * t)) * ψ (g * archRot w hw t)) α, add_zero]
        have := hP.intervalIntegral_add_eq α 0
        rw [zero_add] at this
        exact this

theorem continuous_Pn (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ) :
    Continuous (Pn w hw n ψ) := by
  unfold Pn
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((continuous_expChar n).comp continuous_snd).mul
    (hψ.comp (continuous_fst.mul ((continuous_archRot w hw).comp continuous_snd)))

theorem Pn_mul_left_of_forall (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ} {a : AdelicGL2 (𝓞 F) F}
    (h : ∀ x, ψ (a * x) = ψ x) (g : AdelicGL2 (𝓞 F) F) :
    Pn w hw n ψ (a * g) = Pn w hw n ψ g := by
  simp only [Pn_apply, mul_assoc, h]

theorem Pn_mul_left_of_forall_mul (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ} {a : AdelicGL2 (𝓞 F) F}
    {c : ℂ} (h : ∀ x, ψ (a * x) = c * ψ x) (g : AdelicGL2 (𝓞 F) F) :
    Pn w hw n ψ (a * g) = c * Pn w hw n ψ g := by
  simp only [Pn_apply, mul_assoc, h]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  ring

theorem Pn_mul_right_of_glArch_eq_one (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ} {u : AdelicGL2 (𝓞 F) F}
    (hu : glArch (𝓞 F) F u = 1) (h : ∀ x, ψ (x * u) = ψ x) (g : AdelicGL2 (𝓞 F) F) :
    Pn w hw n ψ (g * u) = Pn w hw n ψ g := by
  simp only [Pn_apply]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [mul_assoc g u (archRot w hw θ), commute_of_glArch_eq_one_of_glFin_eq_one hu (glFin_archRot w hw θ),
    ← mul_assoc g, h]

theorem sum_Pn_mul_right (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ)
    {m : ℕ} (reps : Fin m → AdelicGL2 (𝓞 F) F) (hreps : ∀ i, glArch (𝓞 F) F (reps i) = 1)
    (g : AdelicGL2 (𝓞 F) F) :
    ∑ i, Pn w hw n ψ (g * reps i) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        Complex.exp (-(Complex.I * n * θ)) * ∑ i, ψ (g * archRot w hw θ * reps i) := by
  simp only [Pn_apply]
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro θ _
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc g (reps i) (archRot w hw θ),
      commute_of_glArch_eq_one_of_glFin_eq_one (hreps i) (glFin_archRot w hw θ), ← mul_assoc g]
  · intro i _
    apply Continuous.intervalIntegrable
    have h1 : Continuous fun θ : ℝ => g * reps i * archRot w hw θ :=
      continuous_const.mul (continuous_archRot w hw)
    exact (continuous_expChar n).mul (hψ.comp h1)

end FourierAverage

section Norms

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} {hw : w.IsReal}

theorem norm_expChar (n : ℤ) (θ : ℝ) : ‖Complex.exp (-(Complex.I * n * θ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem norm_Pn_le (n : ℤ) (ψ : AdelicGL2 (𝓞 F) F → ℂ) {g : AdelicGL2 (𝓞 F) F} {M : ℝ}
    (hM : ∀ θ : ℝ, ‖ψ (g * archRot w hw θ)‖ ≤ M) :
    ‖Pn w hw n ψ g‖ ≤ M * |2 * Real.pi - 0| := by
  rw [Pn_apply]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro θ _
  rw [norm_mul, norm_expChar, one_mul]
  exact hM θ

end Norms

section Haar

variable {F : Type} [Field F] [NumberField F]

theorem integral_comp_mul_left (h : AdelicGL2 (𝓞 F) F) (G : AdelicGL2 (𝓞 F) F → ℂ) :
    (letI := glBorel (Fin 2) (𝓞 F) F
      ∫ x, G (h * x) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
    (letI := glBorel (Fin 2) (𝓞 F) F
      ∫ x, G x ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  exact MeasureTheory.integral_mul_left_eq_self G h

theorem rightConv_mul_right (φ f : AdelicGL2 (𝓞 F) F → ℂ) (k g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (g * k) = rightConv F φ (fun y => f (k⁻¹ * y)) g := by
  rw [rightConv_apply, rightConv_apply]
  have key : (fun x => φ (g * k * x) * f x) =
      fun x => (fun y => φ (g * y) * f (k⁻¹ * y)) (k * x) := by
    funext x
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [key]
  exact integral_comp_mul_left k (fun y => φ (g * y) * f (k⁻¹ * y))

end Haar

section PnAlgebra

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} {hw : w.IsReal}

theorem Pn_add (n : ℤ) {ψ₁ ψ₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Continuous ψ₁) (h₂ : Continuous ψ₂) :
    Pn w hw n (ψ₁ + ψ₂) = Pn w hw n ψ₁ + Pn w hw n ψ₂ := by
  funext g
  simp only [Pi.add_apply, Pn_apply, mul_add]
  exact intervalIntegral.integral_add
    (((continuous_expChar n).mul (h₁.comp (continuous_const.mul (continuous_archRot w hw)))).intervalIntegrable
      _ _)
    (((continuous_expChar n).mul (h₂.comp (continuous_const.mul (continuous_archRot w hw)))).intervalIntegrable
      _ _)

theorem Pn_smul (n : ℤ) (c : ℂ) (ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    Pn w hw n (c • ψ) = c • Pn w hw n ψ := by
  funext g
  simp only [Pi.smul_apply, smul_eq_mul, Pn_apply]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  ring

theorem Pn_eq_smul_of_hasArchCharacterAt₀ (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hψ : HasArchCharacterAt₀ F w
      ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) ψ) :
    Pn w hw n ψ = (2 * Real.pi : ℂ) • ψ := by
  funext g
  rw [Pi.smul_apply, smul_eq_mul, Pn_apply]
  have hint : ∀ θ : ℝ, Complex.exp (-(Complex.I * n * θ)) * ψ (g * archRot w hw θ) = ψ g := by
    intro θ
    have h := hψ (rotAt F hw (norm_symm_ringEquivRealOfIsReal F hw) θ) g
    rw [MonoidHom.comp_apply, rowIsometrySubgroup₀Map_rotAt, archWeightCharℝ_rotSO_eq_exp] at h
    change ψ (g * archRot w hw θ) = _ at h
    rw [h, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  simp_rw [hint]
  rw [intervalIntegral.integral_const, Complex.real_smul, sub_zero]
  push_cast
  ring

end PnAlgebra

section PnConv

variable {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)

def rotHull (f : AdelicGL2 (𝓞 F) F → ℂ) : Set (AdelicGL2 (𝓞 F) F) :=
  (fun p : ℝ × AdelicGL2 (𝓞 F) F => archRot w hw p.1 * p.2) '' (Set.Icc 0 (2 * Real.pi) ×ˢ tsupport f)

def rotAvgL (n : ℤ) (f : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(Complex.I * n * θ)) * f ((archRot w hw θ)⁻¹ * x)

def rotAvgArch (n : ℤ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (z : GL (Fin 2) (InfiniteAdeleRing F)) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    Complex.exp (-(Complex.I * n * θ)) * fa ((glArch (𝓞 F) F (archRot w hw θ))⁻¹ * z)

theorem rotAvgL_apply (n : ℤ) (f : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) :
    rotAvgL w hw n f x =
      ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(Complex.I * n * θ)) * f ((archRot w hw θ)⁻¹ * x) := rfl

theorem rotAvgArch_apply (n : ℤ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (z : GL (Fin 2) (InfiniteAdeleRing F)) :
    rotAvgArch w hw n fa z =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        Complex.exp (-(Complex.I * n * θ)) * fa ((glArch (𝓞 F) F (archRot w hw θ))⁻¹ * z) := rfl

variable {w hw}

theorem archRot_mul_adelicArchGLInclAt_of_ne {v : InfinitePlace F} (hvw : v ≠ w) (a : GL (Fin 2) v.Completion)
    (θ : ℝ) : archRot w hw θ * adelicArchGLInclAt F v a = adelicArchGLInclAt F v a * archRot w hw θ := by
  unfold archRot
  exact (commute_adelicArchGLInclAt_of_ne F hvw a _).eq.symm

theorem archRot_mul_rowIsometryInclAt₀_of_ne {v : InfinitePlace F} (hvw : v ≠ w)
    (k : rowIsometrySubgroup₀ v.Completion) (θ : ℝ) :
    archRot w hw θ * rowIsometryInclAt₀ F v k = rowIsometryInclAt₀ F v k * archRot w hw θ :=
  archRot_mul_adelicArchGLInclAt_of_ne hvw _ θ

theorem archRot_mul_rowIsometryInclAt₀_self (k : rowIsometrySubgroup₀ w.Completion) (θ : ℝ) :
    archRot w hw θ * rowIsometryInclAt₀ F w k = rowIsometryInclAt₀ F w k * archRot w hw θ := by
  obtain ⟨α, rfl⟩ := exists_rotAt_eq hw (norm_symm_ringEquivRealOfIsReal F hw) k
  show archRot w hw θ * archRot w hw α = archRot w hw α * archRot w hw θ
  rw [← archRot_add, ← archRot_add, add_comm]

theorem archRot_mul_rowIsometryInclAt₀ (v : InfinitePlace F) (k : rowIsometrySubgroup₀ v.Completion) (θ : ℝ) :
    archRot w hw θ * rowIsometryInclAt₀ F v k = rowIsometryInclAt₀ F v k * archRot w hw θ := by
  by_cases hvw : v = w
  · subst hvw
    exact archRot_mul_rowIsometryInclAt₀_self k θ
  · exact archRot_mul_rowIsometryInclAt₀_of_ne hvw k θ

theorem rotAvgL_add (n : ℤ) {f₁ f₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Continuous f₁) (h₂ : Continuous f₂) :
    rotAvgL w hw n (f₁ + f₂) = rotAvgL w hw n f₁ + rotAvgL w hw n f₂ := by
  funext x
  simp only [Pi.add_apply, rotAvgL_apply, mul_add]
  have hc : ∀ {f : AdelicGL2 (𝓞 F) F → ℂ}, Continuous f → Continuous fun θ : ℝ =>
      Complex.exp (-(Complex.I * n * θ)) * f ((archRot w hw θ)⁻¹ * x) := fun hf =>
    (continuous_expChar n).mul (hf.comp (((continuous_archRot w hw).inv).mul continuous_const))
  exact intervalIntegral.integral_add ((hc h₁).intervalIntegrable _ _) ((hc h₂).intervalIntegrable _ _)

theorem rotAvgL_smul (n : ℤ) (c : ℂ) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    rotAvgL w hw n (c • f) = c • rotAvgL w hw n f := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, rotAvgL_apply]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  ring

theorem rotAvgL_comp_mul_left_of_commute (n : ℤ) (f : AdelicGL2 (𝓞 F) F → ℂ) {h : AdelicGL2 (𝓞 F) F}
    (hh : ∀ θ : ℝ, archRot w hw θ * h = h * archRot w hw θ) :
    rotAvgL w hw n (fun y => f (h⁻¹ * y)) = fun y => rotAvgL w hw n f (h⁻¹ * y) := by
  funext y
  simp only [rotAvgL_apply]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [← mul_assoc, ← mul_assoc, ← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hh θ]

theorem rotAvgL_tensor (n : ℤ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) → ℂ) :
    rotAvgL w hw n (fun x => fa (glArch (𝓞 F) F x) * ff (glFin (𝓞 F) F x)) =
      fun x => rotAvgArch w hw n fa (glArch (𝓞 F) F x) * ff (glFin (𝓞 F) F x) := by
  funext x
  rw [rotAvgL_apply, rotAvgArch_apply, ← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [map_mul, map_inv, glFin_archRot, inv_one, one_mul]
  ring

theorem isCompact_rotHull {f : AdelicGL2 (𝓞 F) F → ℂ} (hfs : HasCompactSupport f) : IsCompact (rotHull w hw f) :=
  (isCompact_Icc.prod hfs).image (((continuous_archRot w hw).comp continuous_fst).mul continuous_snd)

theorem mem_rotHull_of_ne_zero (f : AdelicGL2 (𝓞 F) F → ℂ) (θ : ℝ) (x : AdelicGL2 (𝓞 F) F)
    (hx : f ((archRot w hw θ)⁻¹ * x) ≠ 0) : x ∈ rotHull w hw f := by
  obtain ⟨θ', hθ', hθθ'⟩ := (archRot_periodic w hw).exists_mem_Ico₀ Real.two_pi_pos θ
  refine ⟨(θ', (archRot w hw θ)⁻¹ * x), ⟨Set.Ico_subset_Icc_self hθ', subset_tsupport _ hx⟩, ?_⟩
  show archRot w hw θ' * ((archRot w hw θ)⁻¹ * x) = x
  rw [← hθθ', mul_inv_cancel_left]

theorem eq_zero_of_not_mem_rotHull (f : AdelicGL2 (𝓞 F) F → ℂ) (θ : ℝ) (x : AdelicGL2 (𝓞 F) F)
    (hx : x ∉ rotHull w hw f) : f ((archRot w hw θ)⁻¹ * x) = 0 := by
  by_contra h
  exact hx (mem_rotHull_of_ne_zero f θ x h)

theorem exists_ne_zero_of_rotAvgL_ne_zero (n : ℤ) (f : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F)
    (hx : rotAvgL w hw n f x ≠ 0) : ∃ θ : ℝ, f ((archRot w hw θ)⁻¹ * x) ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  rw [rotAvgL_apply]
  simp only [h, mul_zero]
  exact intervalIntegral.integral_zero

theorem rotAvgL_eq_zero_of_not_mem_rotHull (n : ℤ) (f : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F)
    (hx : x ∉ rotHull w hw f) : rotAvgL w hw n f x = 0 := by
  by_contra h
  obtain ⟨θ, hθ⟩ := exists_ne_zero_of_rotAvgL_ne_zero n f x h
  exact hθ (eq_zero_of_not_mem_rotHull f θ x hx)

theorem hasCompactSupport_rotAvgL (n : ℤ) {f : AdelicGL2 (𝓞 F) F → ℂ} (hfs : HasCompactSupport f) :
    HasCompactSupport (rotAvgL w hw n f) :=
  HasCompactSupport.intro (isCompact_rotHull hfs) fun x hx => rotAvgL_eq_zero_of_not_mem_rotHull n f x hx

theorem continuous_rotAvgL (n : ℤ) {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : Continuous f) :
    Continuous (rotAvgL w hw n f) := by
  unfold rotAvgL
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((continuous_expChar n).comp continuous_snd).mul
    (hf.comp ((((continuous_archRot w hw).comp continuous_snd).inv).mul continuous_fst))

theorem rotAvgL_mul_left_of_glArch_eq_one (n : ℤ) {f : AdelicGL2 (𝓞 F) F → ℂ} {k : AdelicGL2 (𝓞 F) F}
    (hk : glArch (𝓞 F) F k = 1) (h : ∀ x, f (k * x) = f x) (x : AdelicGL2 (𝓞 F) F) :
    rotAvgL w hw n f (k * x) = rotAvgL w hw n f x := by
  simp only [rotAvgL_apply]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [archRot_inv, ← mul_assoc, ← commute_of_glArch_eq_one_of_glFin_eq_one hk (glFin_archRot w hw (-θ)),
    mul_assoc k, h]

theorem rotAvgL_support (n : ℤ) {f : AdelicGL2 (𝓞 F) F → ℂ} {S : Set (AdelicGL2 (𝓞 F) F)}
    (hf : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ k ∈ S ∧ x = a * k)
    (x : AdelicGL2 (𝓞 F) F) (hx : rotAvgL w hw n f x ≠ 0) :
    ∃ a k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ k ∈ S ∧ x = a * k := by
  obtain ⟨θ, hθ⟩ := exists_ne_zero_of_rotAvgL_ne_zero n f x hx
  obtain ⟨a, k, ha, hk, hak⟩ := hf _ hθ
  refine ⟨archRot w hw θ * a, k, by rw [map_mul, glFin_archRot, ha, one_mul], hk, ?_⟩
  rw [mul_assoc, ← hak, mul_inv_cancel_left]

theorem glArch_adelicArchGLInclAt_eq (v : InfinitePlace F) (k : GL (Fin 2) v.Completion) :
    glArch (𝓞 F) F (adelicArchGLInclAt F v k) = archGLIncl F v k := by
  show glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F v k)) = _
  rw [glArch_adelicArchGLIncl]

theorem glArch_archRot (θ : ℝ) :
    glArch (𝓞 F) F (archRot w hw θ) =
      archGLIncl F w ((rotAt F hw (norm_symm_ringEquivRealOfIsReal F hw) θ : rowIsometrySubgroup₀ w.Completion) :
        GL (Fin 2) w.Completion) :=
  glArch_adelicArchGLInclAt_eq w _

theorem glArch_archRot_inv (θ : ℝ) :
    (glArch (𝓞 F) F (archRot w hw θ))⁻¹ =
      archGLIncl F w ((rotAt F hw (norm_symm_ringEquivRealOfIsReal F hw) (-θ) : rowIsometrySubgroup₀ w.Completion) :
        GL (Fin 2) w.Completion) := by
  rw [← map_inv, archRot_inv, glArch_archRot]

omit [NumberField F] in

theorem isRowIsometry_rotAt (θ : ℝ) :
    IsRowIsometry ((rotAt F hw (norm_symm_ringEquivRealOfIsReal F hw) θ : rowIsometrySubgroup₀ w.Completion) :
      GL (Fin 2) w.Completion) :=
  ((mem_rowIsometrySubgroup₀_iff _).1 (rotAt F hw (norm_symm_ringEquivRealOfIsReal F hw) θ).2).2

theorem rotAvgArch_eq_integral_archGLIncl (n : ℤ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (z : GL (Fin 2) (InfiniteAdeleRing F)) :
    rotAvgArch w hw n fa z =
      ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(Complex.I * n * θ)) *
        fa (archGLIncl F w ((rotAt F hw (norm_symm_ringEquivRealOfIsReal F hw) (-θ) :
          rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) * z) := by
  simp only [rotAvgArch_apply, glArch_archRot_inv]

theorem continuous_glArch_archRot : Continuous fun θ : ℝ => glArch (𝓞 F) F (archRot w hw θ) :=
  (continuous_glArch (𝓞 F) F).comp (continuous_archRot w hw)

theorem glArch_archRot_periodic : Function.Periodic (fun θ : ℝ => glArch (𝓞 F) F (archRot w hw θ)) (2 * Real.pi) :=
  fun θ => by simp only [archRot_periodic w hw θ]

theorem glArch_archRot_mul_archGLIncl_of_ne {v : InfinitePlace F} (hvw : v ≠ w) (k : GL (Fin 2) v.Completion) (θ : ℝ) :
    glArch (𝓞 F) F (archRot w hw θ) * archGLIncl F v k = archGLIncl F v k * glArch (𝓞 F) F (archRot w hw θ) := by
  rw [← glArch_adelicArchGLInclAt_eq, ← map_mul, ← map_mul, archRot_mul_adelicArchGLInclAt_of_ne hvw]

theorem glArch_archRot_mul_archGLIncl_self (k : rowIsometrySubgroup₀ w.Completion) (θ : ℝ) :
    glArch (𝓞 F) F (archRot w hw θ) * archGLIncl F w (k : GL (Fin 2) w.Completion) =
      archGLIncl F w (k : GL (Fin 2) w.Completion) * glArch (𝓞 F) F (archRot w hw θ) := by
  rw [← glArch_adelicArchGLInclAt_eq, ← map_mul, ← map_mul]
  exact congrArg _ (archRot_mul_rowIsometryInclAt₀_self k θ)

theorem glArch_archRot_mul_archGLIncl (v : InfinitePlace F) (k : rowIsometrySubgroup₀ v.Completion) (θ : ℝ) :
    glArch (𝓞 F) F (archRot w hw θ) * archGLIncl F v (k : GL (Fin 2) v.Completion) =
      archGLIncl F v (k : GL (Fin 2) v.Completion) * glArch (𝓞 F) F (archRot w hw θ) := by
  rw [← glArch_adelicArchGLInclAt_eq, ← map_mul, ← map_mul]
  exact congrArg _ (archRot_mul_rowIsometryInclAt₀ v k θ)

theorem rotAvgArch_add (n : ℤ) {fa₁ fa₂ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h₁ : Continuous fa₁)
    (h₂ : Continuous fa₂) : rotAvgArch w hw n (fa₁ + fa₂) = rotAvgArch w hw n fa₁ + rotAvgArch w hw n fa₂ := by
  funext z
  simp only [Pi.add_apply, rotAvgArch_apply, mul_add]
  have hc : ∀ {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}, Continuous fa → Continuous fun θ : ℝ =>
      Complex.exp (-(Complex.I * n * θ)) * fa ((glArch (𝓞 F) F (archRot w hw θ))⁻¹ * z) := fun hf =>
    (continuous_expChar n).mul (hf.comp ((continuous_glArch_archRot.inv).mul continuous_const))
  exact intervalIntegral.integral_add ((hc h₁).intervalIntegrable _ _) ((hc h₂).intervalIntegrable _ _)

theorem rotAvgArch_smul (n : ℤ) (c : ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    rotAvgArch w hw n (c • fa) = c • rotAvgArch w hw n fa := by
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, rotAvgArch_apply]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  ring

theorem continuous_rotAvgArch (n : ℤ) {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : Continuous fa) :
    Continuous (rotAvgArch w hw n fa) := by
  unfold rotAvgArch
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((continuous_expChar n).comp continuous_snd).mul
    (hfa.comp (((continuous_glArch_archRot.comp continuous_snd).inv).mul continuous_fst))

theorem rotAvgArch_mul_right (n : ℤ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    rotAvgArch w hw n (fun x => fa (x * k)) = fun x => rotAvgArch w hw n fa (x * k) := by
  funext x
  simp only [rotAvgArch_apply, mul_assoc]

theorem rotAvgArch_inv_mul_of_commute (n : ℤ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    {h : GL (Fin 2) (InfiniteAdeleRing F)}
    (hh : ∀ θ : ℝ, glArch (𝓞 F) F (archRot w hw θ) * h = h * glArch (𝓞 F) F (archRot w hw θ)) :
    rotAvgArch w hw n (fun x => fa (h⁻¹ * x)) = fun x => rotAvgArch w hw n fa (h⁻¹ * x) := by
  funext x
  simp only [rotAvgArch_apply]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [← mul_assoc, ← mul_assoc, ← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hh θ]

def rotHullArch (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) : Set (GL (Fin 2) (InfiniteAdeleRing F)) :=
  (fun p : ℝ × GL (Fin 2) (InfiniteAdeleRing F) => glArch (𝓞 F) F (archRot w hw p.1) * p.2) ''
    (Set.Icc 0 (2 * Real.pi) ×ˢ tsupport fa)

theorem isCompact_rotHullArch {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfs : HasCompactSupport fa) :
    IsCompact (rotHullArch (w := w) (hw := hw) fa) :=
  (isCompact_Icc.prod hfs).image ((continuous_glArch_archRot.comp continuous_fst).mul continuous_snd)

theorem mem_rotHullArch_of_ne_zero (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (θ : ℝ)
    (x : GL (Fin 2) (InfiniteAdeleRing F)) (hx : fa ((glArch (𝓞 F) F (archRot w hw θ))⁻¹ * x) ≠ 0) :
    x ∈ rotHullArch (w := w) (hw := hw) fa := by
  obtain ⟨θ', hθ', hθθ'⟩ := (glArch_archRot_periodic (w := w) (hw := hw)).exists_mem_Ico₀ Real.two_pi_pos θ
  refine ⟨(θ', (glArch (𝓞 F) F (archRot w hw θ))⁻¹ * x), ⟨Set.Ico_subset_Icc_self hθ', subset_tsupport _ hx⟩, ?_⟩
  show glArch (𝓞 F) F (archRot w hw θ') * ((glArch (𝓞 F) F (archRot w hw θ))⁻¹ * x) = x
  have h : glArch (𝓞 F) F (archRot w hw θ) = glArch (𝓞 F) F (archRot w hw θ') := hθθ'
  rw [← h, mul_inv_cancel_left]

theorem rotAvgArch_eq_zero_of_not_mem_rotHullArch (n : ℤ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (x : GL (Fin 2) (InfiniteAdeleRing F)) (hx : x ∉ rotHullArch (w := w) (hw := hw) fa) :
    rotAvgArch w hw n fa x = 0 := by
  rw [rotAvgArch_apply]
  have h : ∀ θ : ℝ, fa ((glArch (𝓞 F) F (archRot w hw θ))⁻¹ * x) = 0 := fun θ => by
    by_contra h
    exact hx (mem_rotHullArch_of_ne_zero fa θ x h)
  simp only [h, mul_zero]
  exact intervalIntegral.integral_zero

theorem hasCompactSupport_rotAvgArch (n : ℤ) {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfs : HasCompactSupport fa) : HasCompactSupport (rotAvgArch w hw n fa) :=
  HasCompactSupport.intro (isCompact_rotHullArch hfs) fun x hx =>
    rotAvgArch_eq_zero_of_not_mem_rotHullArch n fa x hx

theorem Pn_rightConv (n : ℤ) {φ f : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (hf : Continuous f)
    (hfs : HasCompactSupport f) :
    Pn w hw n (rightConv F φ f) = rightConv F φ (rotAvgL w hw n f) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set ν : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hν
  funext g
  have hle : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
  haveI : Fact (volume (Set.Ioc (0 : ℝ) (2 * Real.pi)) < ⊤) := ⟨measure_Ioc_lt_top⟩

  set K : Set (AdelicGL2 (𝓞 F) F) := rotHull w hw f with hK
  have hKc : IsCompact K := isCompact_rotHull hfs
  have hmemK : ∀ (θ : ℝ) (x : AdelicGL2 (𝓞 F) F), f ((archRot w hw θ)⁻¹ * x) ≠ 0 → x ∈ K :=
    fun θ x hx => mem_rotHull_of_ne_zero f θ x hx
  haveI : Fact (ν K < ⊤) := ⟨hKc.measure_lt_top⟩

  set H : AdelicGL2 (𝓞 F) F → ℝ → ℂ := fun x θ =>
    φ (g * x) * (Complex.exp (-(Complex.I * n * θ)) * f ((archRot w hw θ)⁻¹ * x)) with hH
  have hHc : Continuous (Function.uncurry H) := by
    refine (hφ.comp (continuous_const.mul continuous_fst)).mul
      (((continuous_expChar n).comp continuous_snd).mul (hf.comp ?_))
    exact ((continuous_archRot w hw).comp continuous_snd).inv.mul continuous_fst
  obtain ⟨Mφ, hMφ⟩ := hKc.exists_bound_of_continuousOn
    (f := fun x => φ (g * x)) (hφ.comp (continuous_const.mul continuous_id)).continuousOn
  obtain ⟨Mf, hMf⟩ := hfs.exists_bound_of_continuous hf
  have hbound : ∀ p : AdelicGL2 (𝓞 F) F × ℝ, ‖Function.uncurry H p‖ ≤ max Mφ 0 * Mf := by
    rintro ⟨x, θ⟩
    simp only [Function.uncurry_apply_pair, hH, norm_mul, norm_expChar, one_mul]
    by_cases hx : f ((archRot w hw θ)⁻¹ * x) = 0
    · rw [hx, norm_zero, mul_zero]
      exact mul_nonneg (le_max_right _ _) ((norm_nonneg _).trans (hMf 1))
    · exact mul_le_mul ((hMφ x (hmemK θ x hx)).trans (le_max_left _ _)) (hMf _) (norm_nonneg _)
        (le_max_right _ _)
  have hint : Integrable (Function.uncurry H)
      ((ν.restrict K).prod ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))) :=
    Integrable.of_bound hHc.aestronglyMeasurable _ (Filter.Eventually.of_forall hbound)

  have hH0 : ∀ θ : ℝ, ∀ x ∉ K, H x θ = 0 := by
    intro θ x hx
    have : f ((archRot w hw θ)⁻¹ * x) = 0 := by
      by_contra h
      exact hx (hmemK θ x h)
    simp only [hH, this, mul_zero]
  calc Pn w hw n (rightConv F φ f) g
      = ∫ θ in (0 : ℝ)..2 * Real.pi, ∫ x, H x θ ∂ν := by
        rw [Pn_apply]
        apply intervalIntegral.integral_congr
        intro θ _
        simp only
        rw [rightConv_mul_right, rightConv_apply, ← integral_const_mul]
        congr 1
        funext x
        simp only [hH]
        ring
    _ = ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ∫ x in K, H x θ ∂ν := by
        rw [intervalIntegral.integral_of_le hle]
        congr 1
        funext θ
        exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hH0 θ)).symm
    _ = ∫ x in K, ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), H x θ ∂volume ∂ν :=
        (MeasureTheory.integral_integral_swap hint).symm
    _ = ∫ x, ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), H x θ ∂volume ∂ν := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        simp only [hH0 _ x hx]
        exact integral_zero _ _
    _ = rightConv F φ (rotAvgL w hw n f) g := by
        rw [rightConv_apply]
        congr 1
        funext x
        rw [rotAvgL_apply, intervalIntegral.integral_of_le hle, ← integral_const_mul]

end PnConv

end Ws23.SMinf.Rot

end

end ROT5

section ModPoly

set_option autoImplicit false

open scoped Classical
open MeasureTheory

namespace ArchFiniteVector
namespace Poly

section Checks
end Checks

section SubstFinite

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private def precomp (L : E →ₗ[ℝ] E) : (E → ℝ) →ₐ[ℝ] (E → ℝ) where
  toFun v := v ∘ L
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[scoped simp] private theorem precomp_apply (L : E →ₗ[ℝ] E) (v : E → ℝ) (x : E) :
    precomp L v x = v (L x) := rfl

private def IsSubstFinite (h : E → ℝ) : Prop :=
  ∃ V : Submodule ℝ (E → ℝ), FiniteDimensional ℝ V ∧ h ∈ V ∧
    ∀ L : E →ₗ[ℝ] E, ∀ v ∈ V, precomp L v ∈ V

private theorem IsSubstFinite.mul {h₁ h₂ : E → ℝ} (H₁ : IsSubstFinite h₁) (H₂ : IsSubstFinite h₂) :
    IsSubstFinite (h₁ * h₂) := by
  obtain ⟨V₁, hfd₁, hm₁, hs₁⟩ := H₁
  obtain ⟨V₂, hfd₂, hm₂, hs₂⟩ := H₂
  haveI := hfd₁
  haveI := hfd₂
  refine ⟨V₁ * V₂, ?_, Submodule.mul_mem_mul hm₁ hm₂, ?_⟩
  · exact Module.Finite.iff_fg.mpr
      ((Module.Finite.iff_fg.mp hfd₁).mul (Module.Finite.iff_fg.mp hfd₂))
  · intro L v hv
    refine Submodule.mul_induction_on hv ?_ ?_
    · intro m hm n hn
      rw [map_mul]
      exact Submodule.mul_mem_mul (hs₁ L m hm) (hs₂ L n hn)
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy

private theorem IsSubstFinite.add {h₁ h₂ : E → ℝ} (H₁ : IsSubstFinite h₁) (H₂ : IsSubstFinite h₂) :
    IsSubstFinite (h₁ + h₂) := by
  obtain ⟨V₁, hfd₁, hm₁, hs₁⟩ := H₁
  obtain ⟨V₂, hfd₂, hm₂, hs₂⟩ := H₂
  haveI := hfd₁
  haveI := hfd₂
  refine ⟨V₁ ⊔ V₂, inferInstance, Submodule.add_mem_sup hm₁ hm₂, ?_⟩
  intro L v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  exact Submodule.add_mem_sup (hs₁ L y hy) (hs₂ L z hz)

private theorem IsSubstFinite.const (c : ℝ) : IsSubstFinite (fun _ : E => c) := by
  refine ⟨Submodule.span ℝ {fun _ : E => (1 : ℝ)}, ?_, ?_, ?_⟩
  · exact FiniteDimensional.span_of_finite ℝ (Set.finite_singleton _)
  · have h1 : (fun _ : E => c) = c • (fun _ : E => (1 : ℝ)) := by
      funext x
      simp
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · intro L v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have h2 : precomp L (a • fun _ : E => (1 : ℝ)) = a • fun _ : E => (1 : ℝ) := by
      funext x
      simp
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

variable (E) in
private def substFinite : Subalgebra ℝ (E → ℝ) where
  carrier := {h | IsSubstFinite h}
  mul_mem' := IsSubstFinite.mul
  add_mem' := IsSubstFinite.add
  algebraMap_mem' c := by
    have h : (algebraMap ℝ (E → ℝ) c) = fun _ => c := by
      funext x
      simp
    show IsSubstFinite (algebraMap ℝ (E → ℝ) c)
    rw [h]
    exact IsSubstFinite.const c

private theorem IsSubstFinite.linear [FiniteDimensional ℝ E] (ℓ : E →ₗ[ℝ] ℝ) :
    IsSubstFinite (ℓ : E → ℝ) := by
  let b := Module.finBasis ℝ E
  let V : Submodule ℝ (E → ℝ) :=
    Submodule.span ℝ (Set.range fun i => (b.coord i : E → ℝ))
  have key : ∀ f : E →ₗ[ℝ] ℝ, (f : E → ℝ) ∈ V := by
    intro f
    have hf : (f : E → ℝ) = ∑ i, f (b i) • (b.coord i : E → ℝ) := by
      funext m
      rw [Finset.sum_apply]
      conv_lhs => rw [← b.sum_repr m]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_smul, Pi.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
      ring
    rw [hf]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨V, FiniteDimensional.span_of_finite ℝ (Set.finite_range _), key ℓ, ?_⟩
  intro L v hv
  have hle : V.map (precomp L).toLinearMap ≤ V := by
    refine (Submodule.map_span_le _ _ _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact key ((b.coord i).comp L)
  exact hle (Submodule.mem_map_of_mem hv)

end SubstFinite

section Poly

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private def smoothSubmodule : Submodule ℝ (E → ℝ) where
  carrier := {w | ContDiff ℝ (⊤ : ℕ∞) w}
  add_mem' {v w} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hw : ContDiff ℝ (⊤ : ℕ∞) w) := by
    show ContDiff ℝ (⊤ : ℕ∞) (v + w)
    exact hv.add hw
  zero_mem' := by
    show ContDiff ℝ (⊤ : ℕ∞) (0 : E → ℝ)
    exact contDiff_const
  smul_mem' c w (hw : ContDiff ℝ (⊤ : ℕ∞) w) := by
    show ContDiff ℝ (⊤ : ℕ∞) (c • w)
    exact contDiff_const.smul hw

variable {E} in
private theorem IsSubstFinite.exists_smooth_span {p : E → ℝ} (hs : IsSubstFinite p) (hp : ContDiff ℝ (⊤ : ℕ∞) p) :
    ∃ (n : ℕ) (b : Fin n → E → ℝ), (∀ i, ContDiff ℝ (⊤ : ℕ∞) (b i)) ∧
      ∀ L : E →ₗ[ℝ] E, (p ∘ L) ∈ Submodule.span ℝ (Set.range b) := by
  obtain ⟨V, hfd, hpV, hst⟩ := hs
  haveI := hfd
  let W : Submodule ℝ (E → ℝ) := Submodule.span ℝ (Set.range fun L : E →ₗ[ℝ] E => precomp L p)
  have hWV : W ≤ V := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨L, rfl⟩
    exact hst L p hpV
  haveI : FiniteDimensional ℝ W := Submodule.finiteDimensional_of_le hWV
  have hWsmooth : W ≤ smoothSubmodule E := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨L, rfl⟩
    show ContDiff ℝ (⊤ : ℕ∞) (p ∘ L)
    exact hp.comp (LinearMap.toContinuousLinearMap L).contDiff
  let bW := Module.finBasis ℝ W
  refine ⟨Module.finrank ℝ W, fun i => (bW i : E → ℝ), fun i => hWsmooth (bW i).2, fun L => ?_⟩
  have hmem : precomp L p ∈ W := Submodule.subset_span ⟨L, rfl⟩
  have hrepr := bW.sum_repr ⟨precomp L p, hmem⟩
  have hsum : (p ∘ L : E → ℝ) = ∑ i, bW.repr ⟨precomp L p, hmem⟩ i • (bW i : E → ℝ) := by
    have h := congrArg (W.subtype) hrepr
    rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    exact h.symm
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private def coordC (ℓ : E →ₗ[ℝ] ℝ) : C(E, ℝ) := ⟨ℓ, ℓ.continuous_of_finiteDimensional⟩

@[scoped simp] private theorem coordC_apply (ℓ : E →ₗ[ℝ] ℝ) (x : E) : coordC E ℓ x = ℓ x := rfl

private def polyAlg : Subalgebra ℝ C(E, ℝ) :=
  Algebra.adjoin ℝ (Set.range fun ℓ : E →ₗ[ℝ] ℝ => coordC E ℓ)

private def goodAlg : Subalgebra ℝ C(E, ℝ) where
  carrier := {p | ContDiff ℝ (⊤ : ℕ∞) (p : E → ℝ) ∧ IsSubstFinite (p : E → ℝ)}
  mul_mem' := fun {p q} hp hq => ⟨hp.1.mul hq.1, hp.2.mul hq.2⟩
  add_mem' := fun {p q} hp hq => ⟨hp.1.add hq.1, hp.2.add hq.2⟩
  algebraMap_mem' c := by
    have h : ((algebraMap ℝ C(E, ℝ) c : C(E, ℝ)) : E → ℝ) = fun _ => c := by
      funext x
      simp [Algebra.algebraMap_eq_smul_one]
    refine ⟨?_, ?_⟩
    · rw [h]
      exact contDiff_const
    · rw [h]
      exact IsSubstFinite.const c

private theorem polyAlg_le_goodAlg : polyAlg E ≤ goodAlg E := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨ℓ, rfl⟩
  refine ⟨?_, ?_⟩
  · have h : ((coordC E ℓ : C(E, ℝ)) : E → ℝ) = (LinearMap.toContinuousLinearMap ℓ : E → ℝ) := by
      funext x
      simp
    rw [h]
    exact (LinearMap.toContinuousLinearMap ℓ).contDiff
  · exact IsSubstFinite.linear ℓ

private theorem polyAlg_separatesPoints : (polyAlg E).SeparatesPoints := by
  intro x y hxy
  let b := Module.finBasis ℝ E
  have hex : ∃ i, b.repr x i ≠ b.repr y i :=
    not_forall.mp fun h => hxy (b.ext_elem_iff.mpr h)
  obtain ⟨i, hi⟩ := hex
  refine ⟨coordC E (b.coord i), ⟨coordC E (b.coord i), Algebra.subset_adjoin ⟨b.coord i, rfl⟩, rfl⟩,
    ?_⟩
  show b.coord i x ≠ b.coord i y
  simpa [Module.Basis.coord_apply] using hi

private theorem exists_poly_near (K : Set E) (hK : IsCompact K) (Φ : E → ℝ) (hΦ : Continuous Φ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ IsSubstFinite p ∧ ∀ x ∈ K, ‖p x - Φ x‖ < ε := by
  obtain ⟨g, hg, happrox⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (polyAlg_separatesPoints E) (⟨Φ, hΦ⟩ : C(E, ℝ)) hK hε
  exact ⟨g, (polyAlg_le_goodAlg E hg).1, (polyAlg_le_goodAlg E hg).2, fun x hx => happrox x hx⟩

private theorem exists_poly_pair_near (K : Set E) (hK : IsCompact K) (Φ : E → ℂ) (hΦ : Continuous Φ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ IsSubstFinite p ∧ ContDiff ℝ (⊤ : ℕ∞) q ∧
      IsSubstFinite q ∧ ∀ x ∈ K, ‖((p x : ℂ) + (q x : ℂ) * Complex.I) - Φ x‖ < ε := by
  obtain ⟨p, hp1, hp2, hp3⟩ := exists_poly_near E K hK (fun x => (Φ x).re)
    (Complex.continuous_re.comp hΦ) (ε / 2) (half_pos hε)
  obtain ⟨q, hq1, hq2, hq3⟩ := exists_poly_near E K hK (fun x => (Φ x).im)
    (Complex.continuous_im.comp hΦ) (ε / 2) (half_pos hε)
  refine ⟨p, q, hp1, hp2, hq1, hq2, fun x hx => ?_⟩
  have hre : |p x - (Φ x).re| < ε / 2 := by simpa [Real.norm_eq_abs] using hp3 x hx
  have him : |q x - (Φ x).im| < ε / 2 := by simpa [Real.norm_eq_abs] using hq3 x hx
  set z : ℂ := ((p x : ℂ) + (q x : ℂ) * Complex.I) - Φ x with hz
  have hzre : z.re = p x - (Φ x).re := by simp [hz]
  have hzim : z.im = q x - (Φ x).im := by simp [hz]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ < ε / 2 + ε / 2 := by rw [hzre, hzim]; exact add_lt_add hre him
    _ = ε := by ring

variable {E} in
private theorem isSep_of_mem_polyAlg {L : ℝ → E →ₗ[ℝ] E} (hL : ∀ v : E, Continuous fun θ => L θ v)
    {g : C(E, ℝ)} (hg : g ∈ polyAlg E) : Ws23.SMinf.Sep.IsSep L (g : E → ℝ) := by
  refine Algebra.adjoin_induction (hx := hg) ?_ ?_ ?_ ?_
  · rintro _ ⟨ℓ, rfl⟩
    exact Ws23.SMinf.Sep.IsSep.linear hL ℓ
  · intro c
    have h : ((algebraMap ℝ C(E, ℝ) c : C(E, ℝ)) : E → ℝ) = fun _ => c := by
      funext x
      simp [Algebra.algebraMap_eq_smul_one]
    rw [h]
    exact Ws23.SMinf.Sep.IsSep.const c
  · intro u v _ _ hu hv
    exact hu.add hv
  · intro u v _ _ hu hv
    exact hu.mul hv

private theorem exists_poly_near' (K : Set E) (hK : IsCompact K) (Φ : E → ℝ) (hΦ : Continuous Φ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ IsSubstFinite p ∧
      (∀ L : ℝ → E →ₗ[ℝ] E, (∀ v : E, Continuous fun θ => L θ v) → Ws23.SMinf.Sep.IsSep L p) ∧
      ∀ x ∈ K, ‖p x - Φ x‖ < ε := by
  obtain ⟨g, hg, happrox⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (polyAlg_separatesPoints E) (⟨Φ, hΦ⟩ : C(E, ℝ)) hK hε
  exact ⟨g, (polyAlg_le_goodAlg E hg).1, (polyAlg_le_goodAlg E hg).2, fun L hL => isSep_of_mem_polyAlg hL hg,
    fun x hx => happrox x hx⟩

private theorem exists_poly_pair_near' (K : Set E) (hK : IsCompact K) (Φ : E → ℂ) (hΦ : Continuous Φ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ IsSubstFinite p ∧
      (∀ L : ℝ → E →ₗ[ℝ] E, (∀ v : E, Continuous fun θ => L θ v) → Ws23.SMinf.Sep.IsSep L p) ∧
      ContDiff ℝ (⊤ : ℕ∞) q ∧ IsSubstFinite q ∧
      (∀ L : ℝ → E →ₗ[ℝ] E, (∀ v : E, Continuous fun θ => L θ v) → Ws23.SMinf.Sep.IsSep L q) ∧
      ∀ x ∈ K, ‖((p x : ℂ) + (q x : ℂ) * Complex.I) - Φ x‖ < ε := by
  obtain ⟨p, hp1, hp2, hp4, hp3⟩ := exists_poly_near' E K hK (fun x => (Φ x).re)
    (Complex.continuous_re.comp hΦ) (ε / 2) (half_pos hε)
  obtain ⟨q, hq1, hq2, hq4, hq3⟩ := exists_poly_near' E K hK (fun x => (Φ x).im)
    (Complex.continuous_im.comp hΦ) (ε / 2) (half_pos hε)
  refine ⟨p, q, hp1, hp2, hp4, hq1, hq2, hq4, fun x hx => ?_⟩
  have hre : |p x - (Φ x).re| < ε / 2 := by simpa [Real.norm_eq_abs] using hp3 x hx
  have him : |q x - (Φ x).im| < ε / 2 := by simpa [Real.norm_eq_abs] using hq3 x hx
  set z : ℂ := ((p x : ℂ) + (q x : ℂ) * Complex.I) - Φ x with hz
  have hzre : z.re = p x - (Φ x).re := by simp [hz]
  have hzim : z.im = q x - (Φ x).im := by simp [hz]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ < ε / 2 + ε / 2 := by rw [hzre, hzim]; exact add_lt_add hre him
    _ = ε := by ring

end Poly

section Estimate

variable {G : Type*} [MeasurableSpace G] {μ : Measure G}

private theorem norm_integral_sub_integral_le {w a a' r : G → ℂ} {δ : ℝ}
    (hi : Integrable (fun y => w y * (a y * r y)) μ)
    (hi' : Integrable (fun y => w y * (a' y * r y)) μ)
    (hwr : Integrable (fun y => ‖w y‖ * ‖r y‖) μ)
    (hb : ∀ y, r y ≠ 0 → ‖a y - a' y‖ ≤ δ) :
    ‖(∫ y, w y * (a y * r y) ∂μ) - ∫ y, w y * (a' y * r y) ∂μ‖
      ≤ δ * ∫ y, ‖w y‖ * ‖r y‖ ∂μ := by
  rw [← integral_sub hi hi', ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hwr.const_mul δ) (Filter.Eventually.of_forall fun y => ?_)
  have h1 : w y * (a y * r y) - w y * (a' y * r y) = w y * ((a y - a' y) * r y) := by ring
  rw [h1, norm_mul, norm_mul]
  by_cases hr : r y = 0
  · simp [hr]
  · calc ‖w y‖ * (‖a y - a' y‖ * ‖r y‖) ≤ ‖w y‖ * (δ * ‖r y‖) := by
          gcongr
          exact hb y hr
      _ = δ * (‖w y‖ * ‖r y‖) := by ring

private theorem integral_ne_zero_of_close {w a a' r : G → ℂ} {δ : ℝ}
    (hi : Integrable (fun y => w y * (a y * r y)) μ)
    (hi' : Integrable (fun y => w y * (a' y * r y)) μ)
    (hwr : Integrable (fun y => ‖w y‖ * ‖r y‖) μ)
    (hb : ∀ y, r y ≠ 0 → ‖a y - a' y‖ ≤ δ)
    (hsmall : δ * ∫ y, ‖w y‖ * ‖r y‖ ∂μ < ‖∫ y, w y * (a' y * r y) ∂μ‖) :
    (∫ y, w y * (a y * r y) ∂μ) ≠ 0 := by
  intro h0
  have hle := norm_integral_sub_integral_le (μ := μ) hi hi' hwr hb
  rw [h0, zero_sub, norm_neg] at hle
  exact absurd (lt_of_le_of_lt hle hsmall) (lt_irrefl _)

end Estimate

end ArchFiniteVector.Poly
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector"

end ModPoly
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

section ModPlateau

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.InfinitePlace
p2m_open "NumberField.InfinitePlace.Completion IsDedekindDomain NumberField.InfiniteAdeleRing AutomorphicForm"
open AutomorphicForm.WindowedSiegel Metric Topology

open scoped Classical

namespace ArchFiniteVector
namespace Plateau

section PinChecks
end PinChecks
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

section PerField

variable {K : Type*} [NormedField K]

private def HS (A : Matrix (Fin 2) (Fin 2) K) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

private theorem HS_eq_four (A : Matrix (Fin 2) (Fin 2) K) :
    HS A = ‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) := by
  simp [HS, Fin.sum_univ_two]

private theorem HS_eq (g : GL (Fin 2) K) :
    HS (g : Matrix (Fin 2) (Fin 2) K) =
      ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ^ 2 *
        (topNormSq ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) +
          rowNormSq ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hinv : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (g : Matrix (Fin 2) (Fin 2) K).det⁻¹ • (g : Matrix (Fin 2) (Fin 2) K).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv]
  have hn : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ≠ 0 := norm_ne_zero_iff.mpr hdet
  rw [hinv, Matrix.adjugate_fin_two, HS_eq_four]
  simp [topNormSq, rowNormSq, Matrix.smul_apply, norm_mul, norm_inv, norm_neg]
  field_simp
  ring

private theorem HS_rowIsometry_mul (k g : GL (Fin 2) K) (hk : IsRowIsometry k) :
    HS ((k * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = HS (g : Matrix (Fin 2) (Fin 2) K) := by
  rw [HS_eq, HS_eq, _root_.mul_inv_rev, topNormSq_mul_rowIsometry _ hk.inv,
    rowNormSq_mul_rowIsometry _ hk.inv, Units.val_mul, Matrix.det_mul, norm_mul, hk.1, one_mul]

private theorem HS_mul_rowIsometry (g k : GL (Fin 2) K) (hk : IsRowIsometry k) :
    HS ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = HS (g : Matrix (Fin 2) (Fin 2) K) := by
  rw [HS_eq_four, HS_eq_four, Units.val_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hk.2, hk.2]

end PerField
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

section EntrySpace

variable (F : Type) [Field F] [NumberField F]

private abbrev E : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

private def q (m : mixedEmbedding.mixedSpace F) : ℝ := (∑ v, ‖m.1 v‖ ^ 2) + ∑ v, ‖m.2 v‖ ^ 2

private theorem q_nonneg (m : mixedEmbedding.mixedSpace F) : 0 ≤ q F m :=
  add_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (Finset.sum_nonneg fun _ _ => by positivity)

private theorem sq_fst_le_q (m : mixedEmbedding.mixedSpace F) (v : {w : InfinitePlace F // IsReal w}) :
    ‖m.1 v‖ ^ 2 ≤ q F m :=
  le_add_of_le_of_nonneg
    (Finset.single_le_sum (f := fun v => ‖m.1 v‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ v))
    (Finset.sum_nonneg fun _ _ => by positivity)

private theorem sq_snd_le_q (m : mixedEmbedding.mixedSpace F) (v : {w : InfinitePlace F // IsComplex w}) :
    ‖m.2 v‖ ^ 2 ≤ q F m :=
  le_add_of_nonneg_of_le (Finset.sum_nonneg fun _ _ => by positivity)
    (Finset.single_le_sum (f := fun v => ‖m.2 v‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ v))

private theorem contDiff_q : ContDiff ℝ (⊤ : ℕ∞) (q F) := by
  unfold q
  refine ContDiff.add ?_ ?_
  · exact ContDiff.sum fun v _ => ((contDiff_apply ℝ ℝ v).comp contDiff_fst).norm_sq (𝕜 := ℝ)
  · exact ContDiff.sum fun v _ => ((contDiff_apply ℝ ℂ v).comp contDiff_snd).norm_sq (𝕜 := ℂ)

private theorem q_ringEquiv (x : InfiniteAdeleRing F) :
    q F (InfiniteAdeleRing.ringEquiv_mixedSpace F x) = ∑ w, ‖x w‖ ^ 2 := by
  have h1 : ∀ v : {w : InfinitePlace F // IsReal w},
      ‖extensionEmbeddingOfIsReal v.2 (x v.1)‖ = ‖x v.1‖ := fun v =>
    (isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero (map_zero _) _
  have h2 : ∀ v : {w : InfinitePlace F // IsComplex w},
      ‖extensionEmbedding v.1 (x v.1)‖ = ‖x v.1‖ := fun v =>
    (isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _) _
  simp only [q, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, h1, h2]
  rw [← Fintype.sum_subtype_add_sum_subtype IsReal (fun w => ‖x w‖ ^ 2)]
  congr 1
  exact (Fintype.sum_equiv (Equiv.subtypeEquivRight fun _ => not_isReal_iff_isComplex)
    (fun v => ‖x v.1‖ ^ 2) (fun v => ‖x v.1‖ ^ 2) fun _ => rfl).symm

private def N (M : E F) : ℝ := ∑ i, ∑ j, q F (M i j)

private theorem q_le_N (M : E F) (i j : Fin 2) : q F (M i j) ≤ N F M := by
  unfold N
  calc q F (M i j) ≤ ∑ j', q F (M i j') :=
        Finset.single_le_sum (f := fun j' => q F (M i j')) (fun _ _ => q_nonneg F _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', q F (M i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', q F (M i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => q_nonneg F _) (Finset.mem_univ i)

private theorem contDiff_N : ContDiff ℝ (⊤ : ℕ∞) (N F) := by
  unfold N
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (contDiff_q F).comp ((contDiff_apply ℝ (mixedEmbedding.mixedSpace F) j).comp
      (contDiff_apply ℝ (Fin 2 → mixedEmbedding.mixedSpace F) i))

private theorem norm_le_sqrt_N (M : E F) : ‖M‖ ≤ Real.sqrt (N F M) := by
  have key : ∀ (a : ℝ), 0 ≤ a → a ^ 2 ≤ N F M → a ≤ Real.sqrt (N F M) := fun a ha h =>
    calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
      _ ≤ Real.sqrt (N F M) := Real.sqrt_le_sqrt h
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun v => ?_
    exact key _ (norm_nonneg _) ((sq_fst_le_q F _ v).trans (q_le_N F M i j))
  · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun v => ?_
    exact key _ (norm_nonneg _) ((sq_snd_le_q F _ v).trans (q_le_N F M i j))

private def detE (M : E F) : mixedEmbedding.mixedSpace F := M 0 0 * M 1 1 - M 0 1 * M 1 0

omit [NumberField F] in
private theorem detE_eq_det (M : E F) :
    detE F M = Matrix.det (M : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) := by
  rw [Matrix.det_fin_two]
  rfl

private theorem contDiff_detE : ContDiff ℝ (⊤ : ℕ∞) (detE F) := by
  have hc : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) fun M : E F => M i j := fun i j =>
    (contDiff_apply ℝ (mixedEmbedding.mixedSpace F) j).comp
      (contDiff_apply ℝ (Fin 2 → mixedEmbedding.mixedSpace F) i)
  unfold detE
  exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))

private def PD (M : E F) : ℝ := (∏ v, ‖(detE F M).1 v‖ ^ 2) * ∏ v, ‖(detE F M).2 v‖ ^ 2

private theorem PD_nonneg (M : E F) : 0 ≤ PD F M :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) (Finset.prod_nonneg fun _ _ => by positivity)

private theorem contDiff_PD : ContDiff ℝ (⊤ : ℕ∞) (PD F) := by
  unfold PD
  refine ContDiff.mul ?_ ?_
  · exact contDiff_prod fun v _ =>
      ((contDiff_apply ℝ ℝ v).comp (contDiff_fst.comp (contDiff_detE F))).norm_sq (𝕜 := ℝ)
  · exact contDiff_prod fun v _ =>
      ((contDiff_apply ℝ ℂ v).comp (contDiff_snd.comp (contDiff_detE F))).norm_sq (𝕜 := ℂ)

private theorem isUnit_detE_of_PD_ne_zero {M : E F} (h : PD F M ≠ 0) : IsUnit (detE F M) := by
  have h1 : ∀ v, (detE F M).1 v ≠ 0 := fun v hv => by
    apply h
    unfold PD
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv, norm_zero, zero_pow two_ne_zero]), zero_mul]
  have h2 : ∀ v, (detE F M).2 v ≠ 0 := fun v hv => by
    apply h
    unfold PD
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv, norm_zero, zero_pow two_ne_zero]), mul_zero]
  refine IsUnit.of_mul_eq_one ⟨fun v => ((detE F M).1 v)⁻¹, fun v => ((detE F M).2 v)⁻¹⟩ ?_
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · show (detE F M).1 v * ((detE F M).1 v)⁻¹ = 1
    exact mul_inv_cancel₀ (h1 v)
  · show (detE F M).2 v * ((detE F M).2 v)⁻¹ = 1
    exact mul_inv_cancel₀ (h2 v)

end EntrySpace
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

section Bridges

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
private theorem archEntries_eq_mapMatrix (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    (archEntries F y : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.mapMatrix
        (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  funext i j
  rfl

omit [NumberField F] in
private theorem archComponent_coe (w : InfinitePlace F) (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    ((archComponent F w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) =
      (archEval F w).mapMatrix (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  ext i j
  rfl

private theorem N_archEntries (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    N F (archEntries F y) =
      ∑ w : InfinitePlace F, HS ((archComponent F w y : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) := by
  unfold N HS
  simp only [archEntries_apply, q_ringEquiv]
  calc (∑ i, ∑ j, ∑ w, ‖(y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w‖ ^ 2)
        = ∑ i, ∑ w, ∑ j, ‖(y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ w, ∑ i, ∑ j, ‖(y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w‖ ^ 2 := Finset.sum_comm
    _ = _ := by rfl

omit [NumberField F] in
private theorem detE_archEntries (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    detE F (archEntries F y) =
      InfiniteAdeleRing.ringEquiv_mixedSpace F (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det := by
  rw [detE_eq_det, archEntries_eq_mapMatrix]
  exact (RingHom.map_det _ _).symm

omit [NumberField F] in
private theorem norm_detE_fst (y : GL (Fin 2) (InfiniteAdeleRing F)) (v : {w : InfinitePlace F // IsReal w}) :
    ‖(detE F (archEntries F y)).1 v‖ =
      ‖((archComponent F v.1 y : GL (Fin 2) v.1.Completion) : Matrix (Fin 2) (Fin 2) v.1.Completion).det‖ := by
  rw [detE_archEntries, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  show ‖extensionEmbeddingOfIsReal v.2 ((y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det v.1)‖ = _
  rw [(isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero (map_zero _), archComponent_coe,
    ← RingHom.map_det]
  rfl

omit [NumberField F] in
private theorem norm_detE_snd (y : GL (Fin 2) (InfiniteAdeleRing F)) (v : {w : InfinitePlace F // IsComplex w}) :
    ‖(detE F (archEntries F y)).2 v‖ =
      ‖((archComponent F v.1 y : GL (Fin 2) v.1.Completion) : Matrix (Fin 2) (Fin 2) v.1.Completion).det‖ := by
  rw [detE_archEntries, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  show ‖extensionEmbedding v.1 ((y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det v.1)‖ = _
  rw [(isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _), archComponent_coe,
    ← RingHom.map_det]
  rfl

private theorem PD_archEntries_pos (y : GL (Fin 2) (InfiniteAdeleRing F)) : 0 < PD F (archEntries F y) := by
  unfold PD
  refine mul_pos (Finset.prod_pos fun v _ => ?_) (Finset.prod_pos fun v _ => ?_)
  · rw [norm_detE_fst]
    exact pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)) 2
  · rw [norm_detE_snd]
    exact pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)) 2

variable {F}

omit [NumberField F] in
private theorem norm_det_archComponent_mul (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) (y : GL (Fin 2) (InfiniteAdeleRing F)) (v : InfinitePlace F) :
    ‖((archComponent F v (archGLIncl F w k * y) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion).det‖ =
      ‖((archComponent F v y : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion).det‖ := by
  rw [map_mul]
  by_cases h : v = w
  · subst h
    rw [archComponent_archGLIncl_self, Units.val_mul, Matrix.det_mul, norm_mul, hk.1, one_mul]
  · rw [archComponent_archGLIncl_of_ne F h, one_mul]

private theorem N_archEntries_mul (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    N F (archEntries F (archGLIncl F w k * y)) = N F (archEntries F y) := by
  rw [N_archEntries, N_archEntries]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul]
  by_cases h : v = w
  · subst h
    rw [archComponent_archGLIncl_self]
    exact HS_rowIsometry_mul k _ hk
  · rw [archComponent_archGLIncl_of_ne F h, one_mul]

private theorem PD_archEntries_mul (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    PD F (archEntries F (archGLIncl F w k * y)) = PD F (archEntries F y) := by
  unfold PD
  simp only [norm_detE_fst, norm_detE_snd, norm_det_archComponent_mul w k hk y]

omit [NumberField F] in
private theorem norm_det_archComponent_mul_right (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) (y : GL (Fin 2) (InfiniteAdeleRing F)) (v : InfinitePlace F) :
    ‖((archComponent F v (y * archGLIncl F w k) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion).det‖ =
      ‖((archComponent F v y : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion).det‖ := by
  rw [map_mul]
  by_cases h : v = w
  · subst h
    rw [archComponent_archGLIncl_self, Units.val_mul, Matrix.det_mul, norm_mul, hk.1, mul_one]
  · rw [archComponent_archGLIncl_of_ne F h, mul_one]

private theorem N_archEntries_mul_right (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    N F (archEntries F (y * archGLIncl F w k)) = N F (archEntries F y) := by
  rw [N_archEntries, N_archEntries]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul]
  by_cases h : v = w
  · subst h
    rw [archComponent_archGLIncl_self]
    exact HS_mul_rowIsometry _ k hk
  · rw [archComponent_archGLIncl_of_ne F h, mul_one]

private theorem PD_archEntries_mul_right (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    PD F (archEntries F (y * archGLIncl F w k)) = PD F (archEntries F y) := by
  unfold PD
  simp only [norm_detE_fst, norm_detE_snd, norm_det_archComponent_mul_right w k hk y]

end Bridges
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

section Plateau

private def θup (R t : ℝ) : ℝ := Real.smoothTransition (R + 1 - t)

private def θlow (ε t : ℝ) : ℝ := Real.smoothTransition (2 / ε * t - 1)

private theorem contDiff_θup (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (θup R) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

private theorem contDiff_θlow (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (θlow ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

private theorem θup_eq_one {R t : ℝ} (h : t ≤ R) : θup R t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem θup_eq_zero {R t : ℝ} (h : R + 1 ≤ t) : θup R t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem θlow_eq_one {ε t : ℝ} (hε : 0 < ε) (h : ε ≤ t) : θlow ε t = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have : 2 / ε * t ≥ 2 / ε * ε := mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : 2 / ε * ε = 2 := by field_simp
  linarith

private theorem θlow_eq_zero {ε t : ℝ} (hε : 0 < ε) (h : t ≤ ε / 2) : θlow ε t = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have : 2 / ε * t ≤ 2 / ε * (ε / 2) := mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : 2 / ε * (ε / 2) = 1 := by field_simp
  linarith

variable (F : Type) [Field F] [NumberField F]

private def plateau (R ε : ℝ) (M : E F) : ℝ := θup R (N F M) * θlow ε (PD F M)

private theorem contDiff_plateau (R ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (plateau F R ε) :=
  ((contDiff_θup R).comp (contDiff_N F)).mul ((contDiff_θlow ε).comp (contDiff_PD F))

private theorem plateau_eq_one {R ε : ℝ} (hε : 0 < ε) {M : E F} (hN : N F M ≤ R) (hP : ε ≤ PD F M) :
    plateau F R ε M = 1 := by
  rw [plateau, θup_eq_one hN, θlow_eq_one hε hP, one_mul]

private theorem N_lt_of_plateau_ne_zero {R ε : ℝ} {M : E F} (h : plateau F R ε M ≠ 0) : N F M < R + 1 := by
  by_contra hc
  exact h (by rw [plateau, θup_eq_zero (not_lt.mp hc), zero_mul])

private theorem PD_gt_of_plateau_ne_zero {R ε : ℝ} (hε : 0 < ε) {M : E F} (h : plateau F R ε M ≠ 0) :
    ε / 2 < PD F M := by
  by_contra hc
  exact h (by rw [plateau, θlow_eq_zero hε (not_lt.mp hc), mul_zero])

private def ZE (R ε : ℝ) : Set (E F) := {M | N F M ≤ R + 1 ∧ ε / 2 ≤ PD F M}

private theorem plateau_ne_zero_subset_ZE (R ε : ℝ) (hε : 0 < ε) :
    {M : E F | plateau F R ε M ≠ 0} ⊆ ZE F R ε := fun _ h =>
  ⟨(N_lt_of_plateau_ne_zero F h).le, (PD_gt_of_plateau_ne_zero F hε h).le⟩

private theorem isClosed_ZE (R ε : ℝ) : IsClosed (ZE F R ε) :=
  (isClosed_le (contDiff_N F).continuous continuous_const).inter
    (isClosed_le continuous_const (contDiff_PD F).continuous)

private theorem isCompact_ZE (R ε : ℝ) : IsCompact (ZE F R ε) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_ZE F R ε)
    ((Metric.isBounded_closedBall (x := (0 : E F)) (r := Real.sqrt (R + 1))).subset fun M hM => ?_)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_sqrt_N F M).trans (Real.sqrt_le_sqrt hM.1)

private theorem isUnit_detE_of_mem_ZE {R ε : ℝ} (hε : 0 < ε) {M : E F} (hM : M ∈ ZE F R ε) :
    IsUnit (detE F M) :=
  isUnit_detE_of_PD_ne_zero F (lt_of_lt_of_le (half_pos hε) hM.2).ne'

private theorem plateau_archEntries_mul (R ε : ℝ) (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    plateau F R ε (archEntries F (archGLIncl F w k * y)) = plateau F R ε (archEntries F y) := by
  rw [plateau, plateau, N_archEntries_mul w k hk, PD_archEntries_mul w k hk]

private theorem plateau_archEntries_mul_right (R ε : ℝ) (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    plateau F R ε (archEntries F (y * archGLIncl F w k)) = plateau F R ε (archEntries F y) := by
  rw [plateau, plateau, N_archEntries_mul_right w k hk, PD_archEntries_mul_right w k hk]

end Plateau
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

section Topology

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
private theorem continuous_ringEquiv_mixedSpace : Continuous (ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

omit [NumberField F] in
private theorem continuous_ringEquiv_mixedSpace_symm : Continuous (ringEquiv_mixedSpace F).symm := by
  apply continuous_pi
  intro v
  by_cases hv : IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace F => (ringEquiv_mixedSpace F).symm y v)
        = fun y => (isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace F => z.1 ⟨v, hv⟩)
        ((ringEquiv_mixedSpace F).apply_symm_apply y)
    rw [key]
    exact (isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : IsComplex v := not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace F => (ringEquiv_mixedSpace F).symm y v)
        = fun y => (isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨v, hc⟩) := by
      funext y
      apply (isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace F => z.2 ⟨v, hc⟩)
        ((ringEquiv_mixedSpace F).apply_symm_apply y)
    rw [key]
    exact (isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

omit [NumberField F] in
private def mixedHomeo : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F where
  toEquiv := (ringEquiv_mixedSpace F).toEquiv
  continuous_toFun := continuous_ringEquiv_mixedSpace F
  continuous_invFun := continuous_ringEquiv_mixedSpace_symm F

omit [NumberField F] in
private def matHomeo : (Fin 2 → Fin 2 → InfiniteAdeleRing F) ≃ₜ E F :=
  Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => mixedHomeo F

omit [NumberField F] in
private def pairHomeo :
    (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) × (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))ᵐᵒᵖ)
      ≃ₜ (E F × E F) :=
  Homeomorph.prodCongr (matHomeo F) (MulOpposite.opHomeomorph.symm.trans (matHomeo F))

omit [NumberField F] in
private def J (g : GL (Fin 2) (InfiniteAdeleRing F)) : E F × E F :=
  pairHomeo F (Units.embedProduct _ g)

omit [NumberField F] in
private theorem J_apply (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    J F g = (archEntries F g, archEntries F g⁻¹) := rfl

omit [NumberField F] in
private theorem isClosedEmbedding_J : IsClosedEmbedding (J F) :=
  (pairHomeo F).isClosedEmbedding.comp Units.isClosedEmbedding_embedProduct

omit [NumberField F] in
private theorem continuous_archEntries : Continuous (archEntries F) := by
  have : archEntries F = fun g => (J F g).1 := funext fun g => rfl
  rw [this]
  exact continuous_fst.comp (isClosedEmbedding_J F).continuous

private def Ψinv (m : E F) : E F :=
  fun i j => (Ring.inverse (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) •
    Matrix.adjugate (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) i j

omit [NumberField F] in
private theorem Ψinv_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Ψinv F (archEntries F g) = archEntries F g⁻¹ := by
  set A := (ringEquiv_mixedSpace F).toRingHom.mapMatrix
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hA
  have hAinv : (ringEquiv_mixedSpace F).toRingHom.mapMatrix
      ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = A⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [hA, ← map_mul, Units.inv_mul, map_one]
  have h1 : (archEntries F g⁻¹ : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) = A⁻¹ := by
    rw [archEntries_eq_mapMatrix, hAinv]
  funext i j
  show (Ring.inverse (Matrix.det (archEntries F g : Matrix (Fin 2) (Fin 2) _)) •
      Matrix.adjugate (archEntries F g : Matrix (Fin 2) (Fin 2) _)) i j = archEntries F g⁻¹ i j
  have h2 : archEntries F g⁻¹ i j = (archEntries F g⁻¹ : Matrix (Fin 2) (Fin 2) _) i j := rfl
  rw [h2, h1, archEntries_eq_mapMatrix, ← hA, Matrix.inv_def]

private theorem continuousOn_Ψinv {R ε : ℝ} (hε : 0 < ε) : ContinuousOn (Ψinv F) (ZE F R ε) := by
  intro m hm
  have hunit : IsUnit (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) := by
    rw [← detE_eq_det]
    exact isUnit_detE_of_mem_ZE F hε hm
  obtain ⟨u, hu⟩ := hunit
  apply ContinuousAt.continuousWithinAt
  have hdet : Continuous fun m : E F =>
      Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) :=
    Continuous.matrix_det continuous_id
  have h1 : ContinuousAt (fun m : E F =>
      Ring.inverse (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)))) m := by
    have hi : ContinuousAt Ring.inverse
        (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) :=
      hu ▸ NormedRing.inverse_continuousAt u
    exact hi.comp hdet.continuousAt
  have h2 : Continuous fun m : E F =>
      Matrix.adjugate (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) :=
    Continuous.matrix_adjugate continuous_id
  rw [continuousAt_pi]
  intro i
  rw [continuousAt_pi]
  intro j
  have h3 : ContinuousAt (fun m : E F =>
      Ring.inverse (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) *
        Matrix.adjugate (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) i j) m :=
    h1.mul (h2.matrix_elem i j).continuousAt
  have e : (fun y : E F => Ψinv F y i j) = fun m : E F =>
      Ring.inverse (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) *
        Matrix.adjugate (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) i j := by
    funext y
    simp only [Ψinv, Matrix.smul_apply, smul_eq_mul]
  rw [e]
  exact h3

private theorem hasCompactSupport_of_plateau {R ε : ℝ} (hε : 0 < ε)
    (f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hf : ∀ y, plateau F R ε (archEntries F y) = 0 → f y = 0) : HasCompactSupport f := by
  set T : Set (E F × E F) := ZE F R ε ×ˢ (Ψinv F '' ZE F R ε) with hT
  have hTc : IsCompact T :=
    (isCompact_ZE F R ε).prod ((isCompact_ZE F R ε).image_of_continuousOn (continuousOn_Ψinv F hε))
  have hpre : IsCompact (J F ⁻¹' T) := (isClosedEmbedding_J F).isCompact_preimage hTc
  refine HasCompactSupport.intro' hpre (hTc.isClosed.preimage (isClosedEmbedding_J F).continuous) ?_
  intro y hy
  apply hf
  by_contra hne
  apply hy
  have hZ : archEntries F y ∈ ZE F R ε := plateau_ne_zero_subset_ZE F R ε hε hne
  show J F y ∈ T
  rw [J_apply, hT, Set.mem_prod]
  exact ⟨hZ, ⟨archEntries F y, hZ, Ψinv_archEntries F y⟩⟩

end Topology
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

section Parameters

variable (F : Type) [Field F] [NumberField F]

private theorem exists_R (C : Set (GL (Fin 2) (InfiniteAdeleRing F))) (hC : IsCompact C) :
    ∃ R : ℝ, ∀ y ∈ C, N F (archEntries F y) ≤ R := by
  obtain ⟨R, hR⟩ := hC.bddAbove_image
    (f := fun y => N F (archEntries F y)) ((contDiff_N F).continuous.comp (continuous_archEntries F)).continuousOn
  exact ⟨R, fun y hy => hR ⟨y, hy, rfl⟩⟩

private theorem exists_eps (C : Set (GL (Fin 2) (InfiniteAdeleRing F))) (hC : IsCompact C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ C, ε ≤ PD F (archEntries F y) := by
  by_cases hne : C.Nonempty
  · obtain ⟨y₀, hy₀, hmin⟩ := hC.exists_isMinOn hne
      ((contDiff_PD F).continuous.comp (continuous_archEntries F)).continuousOn
    exact ⟨PD F (archEntries F y₀), PD_archEntries_pos F y₀, fun y hy => hmin hy⟩
  · exact ⟨1, one_pos, fun y hy => (hne ⟨y, hy⟩).elim⟩

private theorem exists_plateau (C : Set (GL (Fin 2) (InfiniteAdeleRing F))) (hC : IsCompact C) :
    ∃ Ψ₀ : E F → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ₀ ∧ (∀ y ∈ C, Ψ₀ (archEntries F y) = 1) ∧
      (∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
        ∀ y, Ψ₀ (archEntries F (archGLIncl F w k * y)) = Ψ₀ (archEntries F y)) ∧
      (∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
        ∀ y, Ψ₀ (archEntries F (y * archGLIncl F w k)) = Ψ₀ (archEntries F y)) ∧
      (∀ f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
        (∀ y, Ψ₀ (archEntries F y) = 0 → f y = 0) → HasCompactSupport f) ∧
      (∃ Kc : Set (E F), IsCompact Kc ∧ ∀ M, Ψ₀ M ≠ 0 → M ∈ Kc) := by
  obtain ⟨R, hR⟩ := exists_R F C hC
  obtain ⟨ε, hε, hP⟩ := exists_eps F C hC
  exact ⟨plateau F R ε, contDiff_plateau F R ε, fun y hy => plateau_eq_one F hε (hR y hy) (hP y hy),
    fun w k hk y => plateau_archEntries_mul F R ε w k hk y,
    fun w k hk y => plateau_archEntries_mul_right F R ε w k hk y,
    fun f hf => hasCompactSupport_of_plateau F hε f hf,
    ⟨ZE F R ε, isCompact_ZE F R ε, fun M hM => plateau_ne_zero_subset_ZE F R ε hε hM⟩⟩

end Parameters
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

end ArchFiniteVector.Plateau
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

end ModPlateau
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

section ModAssembly

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

open scoped Classical

namespace ArchFiniteVector
namespace Assembly

section PinChecks
end PinChecks
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

variable (F : Type) [Field F] [NumberField F]

private abbrev E : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

private def Lsub (A : E F) : E F →ₗ[ℝ] E F where
  toFun M := fun i j => ∑ l, A i l * M l j
  map_add' M M' := by
    funext i j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c M := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm]

omit [NumberField F] in
private theorem Lsub_apply (A M : E F) (i j : Fin 2) : Lsub F A M i j = ∑ l, A i l * M l j := rfl

omit [NumberField F] in
private theorem archEntries_mul (a z : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (a * z) = Lsub F (archEntries F a) (archEntries F z) := by
  funext i j
  rw [Lsub_apply]
  simp only [archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

omit [NumberField F] in
private theorem isRowIsometry_coe_inv {w : InfinitePlace F} (k : rowIsometrySubgroup₀ w.Completion) :
    IsRowIsometry ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :=
  ((mem_rowIsometrySubgroup₀_iff w.Completion).mp (k⁻¹).2).2

private theorem glFin_inv_mul (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : AdelicGL2 (𝓞 F) F) :
    glFin (𝓞 F) F ((rowIsometryInclAt₀ F w k)⁻¹ * y) = glFin (𝓞 F) F y := by
  rw [map_mul, map_inv, glFin_rowIsometryInclAt₀, inv_one, one_mul]

private theorem glArch_inv_mul (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : AdelicGL2 (𝓞 F) F) :
    glArch (𝓞 F) F ((rowIsometryInclAt₀ F w k)⁻¹ * y) =
      archGLIncl F w ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) *
        glArch (𝓞 F) F y := by
  rw [map_mul, ← map_inv, glArch_rowIsometryInclAt₀]
  rfl

private def Tfix (r : AdelicGL2 (𝓞 F) F → ℂ) : (E F → ℝ) →ₗ[ℝ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun v := fun y => (v (archEntries F (glArch (𝓞 F) F y)) : ℂ) * r y
  map_add' v v' := by
    funext y
    simp only [Pi.add_apply, Complex.ofReal_add, add_mul]
  map_smul' c v := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul,
      mul_assoc]

private theorem Tfix_apply (r : AdelicGL2 (𝓞 F) F → ℂ) (v : E F → ℝ) (y : AdelicGL2 (𝓞 F) F) :
    Tfix F r v y = (v (archEntries F (glArch (𝓞 F) F y)) : ℂ) * r y := rfl

private theorem Tfix_mem_span (r : AdelicGL2 (𝓞 F) F → ℂ) {n : ℕ} (b : Fin n → E F → ℝ) {v : E F → ℝ}
    (hv : v ∈ Submodule.span ℝ (Set.range b)) :
    Tfix F r v ∈ Submodule.span ℂ (Set.range fun i => Tfix F r (b i)) := by
  have h1 : Tfix F r v ∈ (Submodule.span ℝ (Set.range b)).map (Tfix F r) := Submodule.mem_map_of_mem hv
  rw [Submodule.map_span, ← Set.range_comp] at h1
  exact Submodule.span_le_restrictScalars ℝ ℂ _ h1

private theorem isArchTestFactor_mul_plateau (Ψ₀ : E F → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ₀)
    (hkill : ∀ f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
      (∀ y, Ψ₀ (archEntries F y) = 0 → f y = 0) → HasCompactSupport f)
    (h : E F → ℂ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    IsArchTestFactor F (fun z => h (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ)) := by
  refine ⟨⟨fun M => h M * (Ψ₀ M : ℂ), hh.mul (Complex.ofRealCLM.contDiff.comp hΨ), fun _ => rfl⟩, ?_⟩
  exact hkill _ fun y hy => by simp only [hy, Complex.ofReal_zero, mul_zero]

private theorem contDiff_ofReal_comp {p : E F → ℝ} (hp : ContDiff ℝ (⊤ : ℕ∞) p) :
    ContDiff ℝ (⊤ : ℕ∞) fun M => (p M : ℂ) :=
  Complex.ofRealCLM.contDiff.comp hp

private theorem contDiff_pair {p q : E F → ℝ} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ContDiff ℝ (⊤ : ℕ∞) fun M => (p M : ℂ) + (q M : ℂ) * Complex.I :=
  (contDiff_ofReal_comp F hp).add ((contDiff_ofReal_comp F hq).mul contDiff_const)

private theorem continuous_and_hasCompactSupport_tensor (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : IsArchTestFactor F fa) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) :
    Continuous (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∧
      HasCompactSupport (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) :=
  continuous_and_hasCompactSupport_of_isFactorizableTestFn F _
    (ArchFiniteVector.ConvHalf.isFactorizableTestFn_mk F fa hfa ff hff)

section Translate

variable {F}
variable (Ψ₀ p q : E F → ℝ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)

private def rfun : AdelicGL2 (𝓞 F) F → ℂ :=
  fun y => (Ψ₀ (archEntries F (glArch (𝓞 F) F y)) : ℂ) * ff (glFin (𝓞 F) F y)

private def ffun : AdelicGL2 (𝓞 F) F → ℂ :=
  fun y => ((p (archEntries F (glArch (𝓞 F) F y)) : ℂ) +
      (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) * Complex.I) *
    (Ψ₀ (archEntries F (glArch (𝓞 F) F y)) : ℂ) * ff (glFin (𝓞 F) F y)

private theorem ffun_eq_tensor : ffun Ψ₀ p q ff = fun g =>
    (fun z => ((p (archEntries F z) : ℂ) + (q (archEntries F z) : ℂ) * Complex.I) *
      (Ψ₀ (archEntries F z) : ℂ)) (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g) := rfl

variable (hΨinv : ∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
  ∀ y, Ψ₀ (archEntries F (archGLIncl F w k * y)) = Ψ₀ (archEntries F y))

include hΨinv in
private theorem ffun_translate (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 F) F) :
    ffun Ψ₀ p q ff ((rowIsometryInclAt₀ F w k)⁻¹ * y) =
      Tfix F (rfun Ψ₀ ff) (p ∘ Lsub F (archEntries F (archGLIncl F w
          ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)))) y +
        Complex.I * Tfix F (rfun Ψ₀ ff) (q ∘ Lsub F (archEntries F (archGLIncl F w
          ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)))) y := by
  rw [Tfix_apply, Tfix_apply]
  unfold ffun rfun
  rw [glFin_inv_mul, glArch_inv_mul, hΨinv w _ (isRowIsometry_coe_inv F k), archEntries_mul]
  simp only [Function.comp_apply]
  ring

include hΨinv in
private theorem ffun_translate_mem_span {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ)
    (hp : ∀ L : E F →ₗ[ℝ] E F, (p ∘ L) ∈ Submodule.span ℝ (Set.range bp))
    (hq : ∀ L : E F →ₗ[ℝ] E F, (q ∘ L) ∈ Submodule.span ℝ (Set.range bq))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (fun y => ffun Ψ₀ p q ff ((rowIsometryInclAt₀ F w k)⁻¹ * y)) ∈
      Submodule.span ℂ (Set.range (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i))
        (fun j => Tfix F (rfun Ψ₀ ff) (bq j)))) := by
  have key : (fun y => ffun Ψ₀ p q ff ((rowIsometryInclAt₀ F w k)⁻¹ * y)) =
      Tfix F (rfun Ψ₀ ff) (p ∘ Lsub F (archEntries F (archGLIncl F w
          ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)))) +
        Complex.I • Tfix F (rfun Ψ₀ ff) (q ∘ Lsub F (archEntries F (archGLIncl F w
          ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)))) := by
    funext y
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact ffun_translate Ψ₀ p q ff hΨinv w k y
  rw [key]
  have hl : Set.range (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) ⊆
      Set.range (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) (fun j => Tfix F (rfun Ψ₀ ff) (bq j))) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castAdd m i, by rw [Fin.append_left]⟩
  have hr : Set.range (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) ⊆
      Set.range (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) (fun j => Tfix F (rfun Ψ₀ ff) (bq j))) := by
    rintro _ ⟨j, rfl⟩
    exact ⟨Fin.natAdd n j, by rw [Fin.append_right]⟩
  refine add_mem ?_ (Submodule.smul_mem _ _ ?_)
  · exact Submodule.span_mono hl (Tfix_mem_span F (rfun Ψ₀ ff) bp (hp _))
  · exact Submodule.span_mono hr (Tfix_mem_span F (rfun Ψ₀ ff) bq (hq _))

end Translate
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

private theorem rightConv_ffun_ne_zero (u₀ : AdelicGL2 (𝓞 F) F → ℂ) (hu₀ : Continuous u₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (Φ₀ : E F → ℂ) (hΦ₀ : ∀ z, fa₀ z = Φ₀ (archEntries F z))
    (hfa₀ : IsArchTestFactor F fa₀)
    (Ψ₀ : E F → ℝ) (hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ₀) (hΨ1 : ∀ z ∈ tsupport fa₀, Ψ₀ (archEntries F z) = 1)
    (hkill : ∀ f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
      (∀ y, Ψ₀ (archEntries F y) = 0 → f y = 0) → HasCompactSupport f)
    (Kc : Set (E F)) (hKc : ∀ M, Ψ₀ M ≠ 0 → M ∈ Kc)
    (p q : E F → ℝ) (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (δ : ℝ)
    (hclose : ∀ M ∈ Kc, ‖((p M : ℂ) + (q M : ℂ) * Complex.I) - Φ₀ M‖ < δ)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hsmall : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      δ * ∫ y, ‖u₀ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) <
        ‖rightConv F u₀ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖) :
    rightConv F u₀ (ffun Ψ₀ p q ff) g₀ ≠ 0 := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have hΨarch : IsArchTestFactor F
      (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ)) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill (fun _ => (1 : ℂ)) contDiff_const
  have hr := continuous_and_hasCompactSupport_tensor F _ hΨarch ff hff
  have hr_eq : (fun g => (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
      (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = rfun Ψ₀ ff := by
    funext g
    simp only [rfun, one_mul]
  rw [hr_eq] at hr
  have hfarch : IsArchTestFactor F (fun z => ((p (archEntries F z) : ℂ) + (q (archEntries F z) : ℂ) *
      Complex.I) * (Ψ₀ (archEntries F z) : ℂ)) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_pair F hp hq)
  have hf := continuous_and_hasCompactSupport_tensor F _ hfarch ff hff
  rw [← ffun_eq_tensor] at hf
  have hf₀ := continuous_and_hasCompactSupport_tensor F fa₀ hfa₀ ff hff
  have hint := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hf.1 hf.2 g₀
  have hint₀ := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hf₀.1 hf₀.2 g₀
  have hintr := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hr.1 hr.2 g₀
  have e1 : (fun y => u₀ (g₀ * y) * ffun Ψ₀ p q ff y) = fun y => u₀ (g₀ * y) *
      ((fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) +
        (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) * Complex.I) y * rfun Ψ₀ ff y) := by
    funext y
    simp only [ffun, rfun]
    ring
  have e0 : (fun y => u₀ (g₀ * y) * (fa₀ (glArch (𝓞 F) F y) * ff (glFin (𝓞 F) F y))) = fun y => u₀ (g₀ * y) *
      (Φ₀ (archEntries F (glArch (𝓞 F) F y)) * rfun Ψ₀ ff y) := by
    funext y
    simp only [rfun]
    by_cases h0 : fa₀ (glArch (𝓞 F) F y) = 0
    · rw [h0, ← hΦ₀, h0]
      ring
    · rw [hΨ1 _ (subset_tsupport _ h0), ← hΦ₀]
      push_cast
      ring
  have hne : rightConv F u₀ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ =
      ∫ y, u₀ (g₀ * y) * (Φ₀ (archEntries F (glArch (𝓞 F) F y)) * rfun Ψ₀ ff y)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [rightConv_apply, ← e0]
  have hgoal : rightConv F u₀ (ffun Ψ₀ p q ff) g₀ =
      ∫ y, u₀ (g₀ * y) * ((fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) +
        (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) * Complex.I) y * rfun Ψ₀ ff y)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [rightConv_apply, ← e1]
  rw [hgoal]
  refine ArchFiniteVector.Poly.integral_ne_zero_of_close (μ := adelicGLHaar (Fin 2) (𝓞 F) F)
    (w := fun y => u₀ (g₀ * y))
    (a := fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) + (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) *
      Complex.I) (a' := fun y => Φ₀ (archEntries F (glArch (𝓞 F) F y))) (r := rfun Ψ₀ ff) (δ := δ)
    (e1 ▸ hint) (e0 ▸ hint₀) ?_ ?_ ?_
  · simpa only [norm_mul] using hintr.norm
  · intro y hy
    have hΨne : Ψ₀ (archEntries F (glArch (𝓞 F) F y)) ≠ 0 := fun h0 => hy (by simp only [rfun, h0,
      Complex.ofReal_zero, zero_mul])
    exact (hclose _ (hKc _ hΨne)).le
  · have h := hsmall
    rw [hne] at h
    exact h

private theorem rightConv_ffun_sub_le (u₀ : AdelicGL2 (𝓞 F) F → ℂ) (hu₀ : Continuous u₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (Φ₀ : E F → ℂ) (hΦ₀ : ∀ z, fa₀ z = Φ₀ (archEntries F z))
    (hfa₀ : IsArchTestFactor F fa₀)
    (Ψ₀ : E F → ℝ) (hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ₀) (hΨ1 : ∀ z ∈ tsupport fa₀, Ψ₀ (archEntries F z) = 1)
    (hkill : ∀ f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
      (∀ y, Ψ₀ (archEntries F y) = 0 → f y = 0) → HasCompactSupport f)
    (Kc : Set (E F)) (hKc : ∀ M, Ψ₀ M ≠ 0 → M ∈ Kc)
    (p q : E F → ℝ) (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (δ : ℝ)
    (hclose : ∀ M ∈ Kc, ‖((p M : ℂ) + (q M : ℂ) * Complex.I) - Φ₀ M‖ < δ)
    (g₀ : AdelicGL2 (𝓞 F) F) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    ‖rightConv F u₀ (ffun Ψ₀ p q ff) g₀ - rightConv F u₀ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖ ≤
      δ * ∫ y, ‖u₀ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have hΨarch : IsArchTestFactor F
      (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ)) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill (fun _ => (1 : ℂ)) contDiff_const
  have hr := continuous_and_hasCompactSupport_tensor F _ hΨarch ff hff
  have hr_eq : (fun g => (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
      (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = rfun Ψ₀ ff := by
    funext g
    simp only [rfun, one_mul]
  rw [hr_eq] at hr
  have hfarch : IsArchTestFactor F (fun z => ((p (archEntries F z) : ℂ) + (q (archEntries F z) : ℂ) *
      Complex.I) * (Ψ₀ (archEntries F z) : ℂ)) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_pair F hp hq)
  have hf := continuous_and_hasCompactSupport_tensor F _ hfarch ff hff
  rw [← ffun_eq_tensor] at hf
  have hf₀ := continuous_and_hasCompactSupport_tensor F fa₀ hfa₀ ff hff
  have hint := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hf.1 hf.2 g₀
  have hint₀ := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hf₀.1 hf₀.2 g₀
  have hintr := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hr.1 hr.2 g₀
  have e1 : (fun y => u₀ (g₀ * y) * ffun Ψ₀ p q ff y) = fun y => u₀ (g₀ * y) *
      ((fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) +
        (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) * Complex.I) y * rfun Ψ₀ ff y) := by
    funext y
    simp only [ffun, rfun]
    ring
  have e0 : (fun y => u₀ (g₀ * y) * (fa₀ (glArch (𝓞 F) F y) * ff (glFin (𝓞 F) F y))) = fun y => u₀ (g₀ * y) *
      (Φ₀ (archEntries F (glArch (𝓞 F) F y)) * rfun Ψ₀ ff y) := by
    funext y
    simp only [rfun]
    by_cases h0 : fa₀ (glArch (𝓞 F) F y) = 0
    · rw [h0, ← hΦ₀, h0]
      ring
    · rw [hΨ1 _ (subset_tsupport _ h0), ← hΦ₀]
      push_cast
      ring
  have hne : rightConv F u₀ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ =
      ∫ y, u₀ (g₀ * y) * (Φ₀ (archEntries F (glArch (𝓞 F) F y)) * rfun Ψ₀ ff y)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [rightConv_apply, ← e0]
  have hgoal : rightConv F u₀ (ffun Ψ₀ p q ff) g₀ =
      ∫ y, u₀ (g₀ * y) * ((fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) +
        (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) * Complex.I) y * rfun Ψ₀ ff y)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [rightConv_apply, ← e1]
  show ‖rightConv F u₀ (ffun Ψ₀ p q ff) g₀ -
      rightConv F u₀ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖ ≤ _
  rw [hgoal, hne]
  refine ArchFiniteVector.Poly.norm_integral_sub_integral_le (μ := adelicGLHaar (Fin 2) (𝓞 F) F)
    (w := fun y => u₀ (g₀ * y))
    (a := fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) + (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) *
      Complex.I) (a' := fun y => Φ₀ (archEntries F (glArch (𝓞 F) F y))) (r := rfun Ψ₀ ff) (δ := δ)
    (e1 ▸ hint) (e0 ▸ hint₀) ?_ ?_
  · simpa only [norm_mul] using hintr.norm
  · intro y hy
    have hΨne : Ψ₀ (archEntries F (glArch (𝓞 F) F y)) ≠ 0 := fun h0 => hy (by simp only [rfun, h0,
      Complex.ofReal_zero, zero_mul])
    exact (hclose _ (hKc _ hΨne)).le

section BiFinite

private def Rsub (A : E F) : E F →ₗ[ℝ] E F where
  toFun M := fun i j => ∑ l, M i l * A l j
  map_add' M M' := by
    funext i j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_mul_assoc]

omit [NumberField F] in
private theorem Rsub_apply (A M : E F) (i j : Fin 2) : Rsub F A M i j = ∑ l, M i l * A l j := rfl

omit [NumberField F] in
private theorem archEntries_mul_right (z a : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (z * a) = Rsub F (archEntries F a) (archEntries F z) := by
  funext i j
  rw [Rsub_apply]
  simp only [archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

section FactorTranslate

variable {F}

omit [NumberField F] in
private theorem isRowIsometry_coe {w : InfinitePlace F} (k : rowIsometrySubgroup₀ w.Completion) :
    IsRowIsometry (k : GL (Fin 2) w.Completion) :=
  ((mem_rowIsometrySubgroup₀_iff w.Completion).mp k.2).2

omit [NumberField F] in
private theorem archRowIsometryInclAt₀_eq (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    archRowIsometryInclAt₀ F w k = archGLIncl F w (k : GL (Fin 2) w.Completion) :=
  rfl

private def TfixA (r : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    (E F → ℝ) →ₗ[ℝ] (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) where
  toFun v := fun z => (v (archEntries F z) : ℂ) * r z
  map_add' v v' := by
    funext z
    simp only [Pi.add_apply, Complex.ofReal_add, add_mul]
  map_smul' c v := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul,
      mul_assoc]

omit [NumberField F] in
private theorem TfixA_apply (r : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (v : E F → ℝ)
    (z : GL (Fin 2) (InfiniteAdeleRing F)) : TfixA r v z = (v (archEntries F z) : ℂ) * r z :=
  rfl

omit [NumberField F] in
private theorem TfixA_mem_span (r : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) {n : ℕ} (b : Fin n → E F → ℝ)
    {v : E F → ℝ} (hv : v ∈ Submodule.span ℝ (Set.range b)) :
    TfixA r v ∈ Submodule.span ℂ (Set.range fun i => TfixA r (b i)) := by
  have h1 : TfixA r v ∈ (Submodule.span ℝ (Set.range b)).map (TfixA r) := Submodule.mem_map_of_mem hv
  rw [Submodule.map_span, ← Set.range_comp] at h1
  exact Submodule.span_le_restrictScalars ℝ ℂ _ h1

variable (Ψ₀ p q : E F → ℝ)

private def rA : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun z => (Ψ₀ (archEntries F z) : ℂ)

private def afun : GL (Fin 2) (InfiniteAdeleRing F) → ℂ :=
  fun z => ((p (archEntries F z) : ℂ) + (q (archEntries F z) : ℂ) * Complex.I) * (Ψ₀ (archEntries F z) : ℂ)

private theorem ffun_eq_afun (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) :
    ffun Ψ₀ p q ff = fun g => afun Ψ₀ p q (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g) :=
  rfl

private def BA {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ) :
    Fin (n + m) → GL (Fin 2) (InfiniteAdeleRing F) → ℂ :=
  Fin.append (fun i => TfixA (rA Ψ₀) (bp i)) (fun j => TfixA (rA Ψ₀) (bq j))

private def BAinv {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ) :
    Fin (n + m) → GL (Fin 2) (InfiniteAdeleRing F) → ℂ :=
  fun i => fun x => BA Ψ₀ bp bq i x⁻¹

omit [NumberField F] in
private theorem mem_span_BA_of_eq {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ) {vp vq : E F → ℝ}
    (hvp : vp ∈ Submodule.span ℝ (Set.range bp)) (hvq : vq ∈ Submodule.span ℝ (Set.range bq))
    {g : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hg : ∀ z, g z = TfixA (rA Ψ₀) vp z + Complex.I * TfixA (rA Ψ₀) vq z) :
    g ∈ Submodule.span ℂ (Set.range (BA Ψ₀ bp bq)) := by
  have key : g = TfixA (rA Ψ₀) vp + Complex.I • TfixA (rA Ψ₀) vq := by
    funext z
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hg z
  rw [key]
  have hl : Set.range (fun i => TfixA (rA Ψ₀) (bp i)) ⊆ Set.range (BA Ψ₀ bp bq) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨Fin.castAdd m i, ?_⟩
    unfold BA
    rw [Fin.append_left]
  have hr : Set.range (fun j => TfixA (rA Ψ₀) (bq j)) ⊆ Set.range (BA Ψ₀ bp bq) := by
    rintro _ ⟨j, rfl⟩
    refine ⟨Fin.natAdd n j, ?_⟩
    unfold BA
    rw [Fin.append_right]
  refine add_mem ?_ (Submodule.smul_mem _ _ ?_)
  · exact Submodule.span_mono hl (TfixA_mem_span (rA Ψ₀) bp hvp)
  · exact Submodule.span_mono hr (TfixA_mem_span (rA Ψ₀) bq hvq)

variable (hΨinv : ∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
  ∀ y, Ψ₀ (archEntries F (archGLIncl F w k * y)) = Ψ₀ (archEntries F y))
variable (hΨinvR : ∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
  ∀ y, Ψ₀ (archEntries F (y * archGLIncl F w k)) = Ψ₀ (archEntries F y))

omit [NumberField F] in
include hΨinv in
private theorem afun_mul_left (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (z : GL (Fin 2) (InfiniteAdeleRing F)) :
    afun Ψ₀ p q (archGLIncl F w k * z) =
      TfixA (rA Ψ₀) (p ∘ Lsub F (archEntries F (archGLIncl F w k))) z +
        Complex.I * TfixA (rA Ψ₀) (q ∘ Lsub F (archEntries F (archGLIncl F w k))) z := by
  rw [TfixA_apply, TfixA_apply]
  unfold afun rA
  rw [hΨinv w k hk z, archEntries_mul]
  simp only [Function.comp_apply]
  ring

omit [NumberField F] in
include hΨinvR in
private theorem afun_mul_right (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (z : GL (Fin 2) (InfiniteAdeleRing F)) :
    afun Ψ₀ p q (z * archGLIncl F w k) =
      TfixA (rA Ψ₀) (p ∘ Rsub F (archEntries F (archGLIncl F w k))) z +
        Complex.I * TfixA (rA Ψ₀) (q ∘ Rsub F (archEntries F (archGLIncl F w k))) z := by
  rw [TfixA_apply, TfixA_apply]
  unfold afun rA
  rw [hΨinvR w k hk z, archEntries_mul_right]
  simp only [Function.comp_apply]
  ring

omit [NumberField F] in
include hΨinv in
private theorem afun_mul_left_mem_span {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ)
    (hp : ∀ L : E F →ₗ[ℝ] E F, (p ∘ L) ∈ Submodule.span ℝ (Set.range bp))
    (hq : ∀ L : E F →ₗ[ℝ] E F, (q ∘ L) ∈ Submodule.span ℝ (Set.range bq))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (fun z => afun Ψ₀ p q (archRowIsometryInclAt₀ F w k * z)) ∈ Submodule.span ℂ (Set.range (BA Ψ₀ bp bq)) :=
  mem_span_BA_of_eq Ψ₀ bp bq (hp _) (hq _) fun z => by
    rw [archRowIsometryInclAt₀_eq]
    exact afun_mul_left Ψ₀ p q hΨinv w _ (isRowIsometry_coe k) z

omit [NumberField F] in
include hΨinvR in
private theorem afun_mul_right_mem_span {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ)
    (hp : ∀ L : E F →ₗ[ℝ] E F, (p ∘ L) ∈ Submodule.span ℝ (Set.range bp))
    (hq : ∀ L : E F →ₗ[ℝ] E F, (q ∘ L) ∈ Submodule.span ℝ (Set.range bq))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (fun z => afun Ψ₀ p q (z * archRowIsometryInclAt₀ F w k)) ∈ Submodule.span ℂ (Set.range (BA Ψ₀ bp bq)) :=
  mem_span_BA_of_eq Ψ₀ bp bq (hp _) (hq _) fun z => by
    rw [archRowIsometryInclAt₀_eq]
    exact afun_mul_right Ψ₀ p q hΨinvR w _ (isRowIsometry_coe k) z

omit [NumberField F] in
include hΨinv in
private theorem afun_inv_mul_mem_span {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ)
    (hp : ∀ L : E F →ₗ[ℝ] E F, (p ∘ L) ∈ Submodule.span ℝ (Set.range bp))
    (hq : ∀ L : E F →ₗ[ℝ] E F, (q ∘ L) ∈ Submodule.span ℝ (Set.range bq))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (fun x => afun Ψ₀ p q (x * archRowIsometryInclAt₀ F w k)⁻¹) ∈
      Submodule.span ℂ (Set.range (BAinv Ψ₀ bp bq)) := by
  have h := afun_mul_left_mem_span Ψ₀ p q hΨinv bp bq hp hq w k⁻¹
  have e : (fun x => afun Ψ₀ p q (x * archRowIsometryInclAt₀ F w k)⁻¹) =
      fun x => (fun z => afun Ψ₀ p q (archRowIsometryInclAt₀ F w k⁻¹ * z)) x⁻¹ := by
    funext x
    simp only [_root_.mul_inv_rev, map_inv]
  rw [e]
  exact ArchFiniteVector.ArchCut.comp_inv_mem_span (BA Ψ₀ bp bq) h

end FactorTranslate
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

omit [NumberField F] in
private theorem exists_archRepAt_of_translates (w : InfinitePlace F) (u : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (W : Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ k : rowIsometrySubgroup₀ w.Completion, (fun x => u (x * archRowIsometryInclAt₀ F w k)) ∈ W) :
    ∃ τ : ArchRepAt F w, u ∈ archFactorTypeSubmoduleAt F w τ := by
  obtain ⟨V, hfin, hu, hV⟩ :=
    ArchFiniteVector.ArchCut.exists_stable_of_translates_mem (archRowIsometryInclAt₀ F w) u W hW
  haveI := hfin
  obtain ⟨n, ρ, hmem⟩ := ArchFiniteVector.ArchCut.exists_rep_mem_typeSubmodule (archRowIsometryInclAt₀ F w) V hu hV
  exact ⟨⟨n, ρ⟩, hmem⟩

omit [NumberField F] in
private theorem exists_archRepAt_dual_of_translates (w : InfinitePlace F) (u : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (W : Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ k : rowIsometrySubgroup₀ w.Completion, (fun x => u (x * archRowIsometryInclAt₀ F w k)) ∈ W) :
    ∃ τ : ArchRepAt F w, u ∈ archFactorDualTypeSubmoduleAt F w τ := by
  obtain ⟨V, hfin, hu, hV⟩ :=
    ArchFiniteVector.ArchCut.exists_stable_of_translates_mem (archRowIsometryInclAt₀ F w) u W hW
  haveI := hfin
  obtain ⟨n, ρ, hmem⟩ :=
    ArchFiniteVector.ArchCut.exists_rep_mem_typeSubmodule_dual (archRowIsometryInclAt₀ F w) V hu hV
  exact ⟨⟨n, ρ⟩, hmem⟩

private def tripleFamily (τ₁ τ₂ τ₃ : ∀ w : InfinitePlace F, ArchRepAt F w) : ArchTypeFamily F where
  card := fun _ => 3
  rep := fun w => ![τ₁ w, τ₂ w, τ₃ w]

omit [NumberField F] in
private theorem mem_archFactorCut_tripleFamily (τ₁ τ₂ τ₃ : ∀ w : InfinitePlace F, ArchRepAt F w)
    {u : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : ∀ w, u ∈ archFactorTypeSubmoduleAt F w (τ₁ w)) :
    u ∈ archFactorCutSubmodule F (tripleFamily F τ₁ τ₂ τ₃) :=
  (Submodule.mem_iInf _).mpr fun w => Submodule.mem_iSup_of_mem (0 : Fin 3) (h w)

omit [NumberField F] in
private theorem mem_archFactorDualCut_tripleFamily (τ₁ τ₂ τ₃ : ∀ w : InfinitePlace F, ArchRepAt F w)
    {u : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : ∀ w, u ∈ archFactorDualTypeSubmoduleAt F w (τ₂ w)) :
    u ∈ archFactorDualCutSubmodule F (tripleFamily F τ₁ τ₂ τ₃) :=
  (Submodule.mem_iInf _).mpr fun w => Submodule.mem_iSup_of_mem (1 : Fin 3) (h w)

private theorem mem_archCut_tripleFamily (τ₁ τ₂ τ₃ : ∀ w : InfinitePlace F, ArchRepAt F w)
    {v : AdelicGL2 (𝓞 F) F → ℂ} (h : ∀ w, v ∈ archTypeSubmoduleAt F w (τ₃ w)) :
    v ∈ archCutSubmodule F (tripleFamily F τ₁ τ₂ τ₃) :=
  (Submodule.mem_iInf _).mpr fun w => Submodule.mem_iSup_of_mem (2 : Fin 3) (h w)

private theorem exists_archFiniteVector (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa₀ : IsArchTestFactor F fa₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ ≠ 0) :
    ∃ (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∈ archCutSubmodule F tys := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  obtain ⟨⟨Φ₀, hΦ₀, hfaΦ⟩, hfa₀c⟩ := id hfa₀
  obtain ⟨Ψ₀, hΨs, hΨ1, hΨinv, hΨinvR, hkill, Kc, hKc, hKcΨ⟩ :=
    ArchFiniteVector.Plateau.exists_plateau F (tsupport fa₀) hfa₀c
  obtain ⟨δ, hδpos, hsmall⟩ : ∃ δ : ℝ, 0 < δ ∧
      δ * (∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) <
        ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖ := by
    set M : ℝ := ∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
    set cc : ℝ := ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖
    have hMnn : 0 ≤ M := integral_nonneg fun y => by positivity
    have hccpos : 0 < cc := norm_pos_iff.mpr hg₀
    have h2 : 0 < 2 * (M + 1) := by linarith
    refine ⟨cc / (2 * (M + 1)), div_pos hccpos h2, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ h2]
    nlinarith
  obtain ⟨p, q, hp, hps, hq, hqs, hclose⟩ :=
    ArchFiniteVector.Poly.exists_poly_pair_near (E F) Kc hKc Φ₀ hΦ₀.continuous δ hδpos
  obtain ⟨n, bp, hbp, hpspan⟩ := hps.exists_smooth_span hp
  obtain ⟨m, bq, hbq, hqspan⟩ := hqs.exists_smooth_span hq
  have hfarch : IsArchTestFactor F (afun Ψ₀ p q) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_pair F hp hq)
  have hune : rightConv F φ (fun g => afun Ψ₀ p q (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 := fun h0 =>
    rightConv_ffun_ne_zero F φ hφ ff hff fa₀ Φ₀ hfaΦ hfa₀ Ψ₀ hΨs hΨ1 hkill Kc hKcΨ p q hp hq δ hclose g₀ hsmall
      (by rw [ffun_eq_afun Ψ₀ p q ff, h0]; rfl)
  have hfs : ∀ i, Continuous (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i))
      (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i) ∧ HasCompactSupport (Fin.append
        (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i) := by
    have key : ∀ (b : E F → ℝ), ContDiff ℝ (⊤ : ℕ∞) b →
        Continuous (Tfix F (rfun Ψ₀ ff) b) ∧ HasCompactSupport (Tfix F (rfun Ψ₀ ff) b) := by
      intro b hb
      have harch : IsArchTestFactor F (fun z => (fun M => (b M : ℂ)) (archEntries F z) *
          (Ψ₀ (archEntries F z) : ℂ)) :=
        isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_ofReal_comp F hb)
      have h := continuous_and_hasCompactSupport_tensor F _ harch ff hff
      have e : (fun g => (fun z => (fun M => (b M : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
          (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = Tfix F (rfun Ψ₀ ff) b := by
        funext g
        rw [Tfix_apply]
        simp only [rfun]
        ring
      rw [e] at h
      exact h
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact key _ (hbp i)
    · rw [Fin.append_right]
      exact key _ (hbq j)
  have hV : ∀ w : InfinitePlace F, ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ V ∧ rightConv F φ (ffun Ψ₀ p q ff) ∈ V ∧
        ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ v ∈ V, (fun x => v (x * rowIsometryInclAt₀ F w k)) ∈ V :=
    fun w => ArchFiniteVector.KFinite.exists_finiteDimensional_mem_of_forall_mem_span F (rowIsometryInclAt₀ F w) φ
      hφ _ (fun i => (hfs i).1) (fun i => (hfs i).2) (ffun Ψ₀ p q ff)
      (ffun_translate_mem_span Ψ₀ p q ff hΨinv bp bq hpspan hqspan w)
  have hτ₃ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w,
      rightConv F φ (ffun Ψ₀ p q ff) ∈ archTypeSubmoduleAt F w τ := by
    intro w
    obtain ⟨V, hfin, hu, hstab⟩ := hV w
    haveI := hfin
    obtain ⟨n', ρ, hmem⟩ :=
      ArchFiniteVector.ArchCut.exists_rep_mem_typeSubmodule (rowIsometryInclAt₀ F w) V hu hstab
    exact ⟨⟨n', ρ⟩, hmem⟩
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (BA Ψ₀ bp bq))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (BAinv Ψ₀ bp bq))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hτ₂ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w, afun Ψ₀ p q ∈ archFactorDualTypeSubmoduleAt F w τ :=
    fun w => exists_archRepAt_dual_of_translates F w (afun Ψ₀ p q) _
      (fun k => afun_mul_right_mem_span Ψ₀ p q hΨinvR bp bq hpspan hqspan w k)
  have hτ₁ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w,
      (fun x => afun Ψ₀ p q x⁻¹) ∈ archFactorTypeSubmoduleAt F w τ :=
    fun w => exists_archRepAt_of_translates F w (fun x => afun Ψ₀ p q x⁻¹) _
      (fun k => afun_inv_mul_mem_span Ψ₀ p q hΨinv bp bq hpspan hqspan w k)
  choose τ₁ hτ₁ using hτ₁
  choose τ₂ hτ₂ using hτ₂
  choose τ₃ hτ₃ using hτ₃
  refine ⟨tripleFamily F τ₁ τ₂ τ₃, afun Ψ₀ p q, hfarch,
    ⟨mem_archFactorCut_tripleFamily F τ₁ τ₂ τ₃ hτ₁, mem_archFactorDualCut_tripleFamily F τ₁ τ₂ τ₃ hτ₂⟩, hune, ?_⟩
  have h3 := mem_archCut_tripleFamily F τ₁ τ₂ τ₃ hτ₃
  rwa [ffun_eq_afun] at h3

open scoped Pointwise in

private theorem exists_archFiniteVector_uniformOn (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa₀ : IsArchTestFactor F fa₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ ≠ 0)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (η : ℝ) (hη : 0 < η) :
    ∃ (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∈ archCutSubmodule F tys ∧
        ∀ g ∈ C, ‖rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g -
            rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g‖ ≤ η := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  obtain ⟨⟨Φ₀, hΦ₀, hfaΦ⟩, hfa₀c⟩ := id hfa₀
  obtain ⟨Ψ₀, hΨs, hΨ1, hΨinv, hΨinvR, hkill, Kc, hKc, hKcΨ⟩ :=
    ArchFiniteVector.Plateau.exists_plateau F (tsupport fa₀) hfa₀c

  have hΨarch' : IsArchTestFactor F
      (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ)) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill (fun _ => (1 : ℂ)) contDiff_const
  have hr' := continuous_and_hasCompactSupport_tensor F _ hΨarch' ff hff
  have hr_eq' : (fun g => (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
      (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = rfun Ψ₀ ff := by
    funext g
    simp only [rfun, one_mul]
  rw [hr_eq'] at hr'
  obtain ⟨Bφ, hBφ⟩ : ∃ B : ℝ, ∀ z ∈ C * tsupport (rfun Ψ₀ ff), ‖φ z‖ ≤ B :=
    (hC.mul hr'.2).exists_bound_of_continuousOn hφ.continuousOn
  set Bst : ℝ := max Bφ 0 with hBst
  set Ir : ℝ := ∫ y, ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with hIr
  have hIr0 : 0 ≤ Ir := integral_nonneg fun _ => norm_nonneg _
  have hBI0 : 0 ≤ Bst * Ir := mul_nonneg (le_max_right _ _) hIr0
  have hM_le : ∀ g ∈ C, (∫ y, ‖φ (g * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) ≤ Bst * Ir := by
    intro g hg
    have hi1 : Integrable (fun y => ‖φ (g * y)‖ * ‖rfun Ψ₀ ff y‖) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
      simpa only [norm_mul] using
        (ArchFiniteVector.KFinite.integrable_rightConv_integrand F φ hφ _ hr'.1 hr'.2 g).norm
    have hi2 : Integrable (fun y => Bst * ‖rfun Ψ₀ ff y‖) (adelicGLHaar (Fin 2) (𝓞 F) F) :=
      ((hr'.1.norm).integrable_of_hasCompactSupport hr'.2.norm).const_mul Bst
    rw [hIr, ← integral_const_mul]
    refine integral_mono hi1 hi2 fun y => ?_
    by_cases hy : y ∈ tsupport (rfun Ψ₀ ff)
    · exact mul_le_mul_of_nonneg_right ((hBφ _ (Set.mul_mem_mul hg hy)).trans (le_max_left _ _)) (norm_nonneg _)
    · have h0 : rfun Ψ₀ ff y = 0 := by
        by_contra h
        exact hy (subset_tsupport _ h)
      simp only [h0, norm_zero, mul_zero, le_refl]
  obtain ⟨δ₁, hδ₁pos, hsmall₁⟩ : ∃ δ : ℝ, 0 < δ ∧
      δ * (∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) <
        ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖ := by
    set M : ℝ := ∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
    set cc : ℝ := ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖
    have hMnn : 0 ≤ M := integral_nonneg fun y => by positivity
    have hccpos : 0 < cc := norm_pos_iff.mpr hg₀
    have h2 : 0 < 2 * (M + 1) := by linarith
    refine ⟨cc / (2 * (M + 1)), div_pos hccpos h2, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ h2]
    nlinarith
  set δ : ℝ := min δ₁ (η / (Bst * Ir + 1)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos (div_pos hη (by linarith))
  have hδle₁ : δ ≤ δ₁ := min_le_left _ _
  have hδle₂ : δ ≤ η / (Bst * Ir + 1) := min_le_right _ _
  have hsmall : δ * (∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) <
      ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖ :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hδle₁ (integral_nonneg fun y => by positivity)) hsmall₁
  obtain ⟨p, q, hp, hps, hq, hqs, hclose⟩ :=
    ArchFiniteVector.Poly.exists_poly_pair_near (E F) Kc hKc Φ₀ hΦ₀.continuous δ hδpos
  obtain ⟨n, bp, hbp, hpspan⟩ := hps.exists_smooth_span hp
  obtain ⟨m, bq, hbq, hqspan⟩ := hqs.exists_smooth_span hq
  have hfarch : IsArchTestFactor F (afun Ψ₀ p q) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_pair F hp hq)
  have hune : rightConv F φ (fun g => afun Ψ₀ p q (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 := fun h0 =>
    rightConv_ffun_ne_zero F φ hφ ff hff fa₀ Φ₀ hfaΦ hfa₀ Ψ₀ hΨs hΨ1 hkill Kc hKcΨ p q hp hq δ hclose g₀ hsmall
      (by rw [ffun_eq_afun Ψ₀ p q ff, h0]; rfl)
  have hfs : ∀ i, Continuous (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i))
      (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i) ∧ HasCompactSupport (Fin.append
        (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i) := by
    have key : ∀ (b : E F → ℝ), ContDiff ℝ (⊤ : ℕ∞) b →
        Continuous (Tfix F (rfun Ψ₀ ff) b) ∧ HasCompactSupport (Tfix F (rfun Ψ₀ ff) b) := by
      intro b hb
      have harch : IsArchTestFactor F (fun z => (fun M => (b M : ℂ)) (archEntries F z) *
          (Ψ₀ (archEntries F z) : ℂ)) :=
        isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_ofReal_comp F hb)
      have h := continuous_and_hasCompactSupport_tensor F _ harch ff hff
      have e : (fun g => (fun z => (fun M => (b M : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
          (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = Tfix F (rfun Ψ₀ ff) b := by
        funext g
        rw [Tfix_apply]
        simp only [rfun]
        ring
      rw [e] at h
      exact h
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact key _ (hbp i)
    · rw [Fin.append_right]
      exact key _ (hbq j)
  have hV : ∀ w : InfinitePlace F, ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ V ∧ rightConv F φ (ffun Ψ₀ p q ff) ∈ V ∧
        ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ v ∈ V, (fun x => v (x * rowIsometryInclAt₀ F w k)) ∈ V :=
    fun w => ArchFiniteVector.KFinite.exists_finiteDimensional_mem_of_forall_mem_span F (rowIsometryInclAt₀ F w) φ
      hφ _ (fun i => (hfs i).1) (fun i => (hfs i).2) (ffun Ψ₀ p q ff)
      (ffun_translate_mem_span Ψ₀ p q ff hΨinv bp bq hpspan hqspan w)
  have hτ₃ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w,
      rightConv F φ (ffun Ψ₀ p q ff) ∈ archTypeSubmoduleAt F w τ := by
    intro w
    obtain ⟨V, hfin, hu, hstab⟩ := hV w
    haveI := hfin
    obtain ⟨n', ρ, hmem⟩ :=
      ArchFiniteVector.ArchCut.exists_rep_mem_typeSubmodule (rowIsometryInclAt₀ F w) V hu hstab
    exact ⟨⟨n', ρ⟩, hmem⟩
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (BA Ψ₀ bp bq))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (BAinv Ψ₀ bp bq))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hτ₂ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w, afun Ψ₀ p q ∈ archFactorDualTypeSubmoduleAt F w τ :=
    fun w => exists_archRepAt_dual_of_translates F w (afun Ψ₀ p q) _
      (fun k => afun_mul_right_mem_span Ψ₀ p q hΨinvR bp bq hpspan hqspan w k)
  have hτ₁ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w,
      (fun x => afun Ψ₀ p q x⁻¹) ∈ archFactorTypeSubmoduleAt F w τ :=
    fun w => exists_archRepAt_of_translates F w (fun x => afun Ψ₀ p q x⁻¹) _
      (fun k => afun_inv_mul_mem_span Ψ₀ p q hΨinv bp bq hpspan hqspan w k)
  choose τ₁ hτ₁ using hτ₁
  choose τ₂ hτ₂ using hτ₂
  choose τ₃ hτ₃ using hτ₃
  refine ⟨tripleFamily F τ₁ τ₂ τ₃, afun Ψ₀ p q, hfarch,
    ⟨mem_archFactorCut_tripleFamily F τ₁ τ₂ τ₃ hτ₁, mem_archFactorDualCut_tripleFamily F τ₁ τ₂ τ₃ hτ₂⟩, hune, ?_, ?_⟩
  · have h3 := mem_archCut_tripleFamily F τ₁ τ₂ τ₃ hτ₃
    rwa [ffun_eq_afun] at h3
  · intro g hg
    have hle := rightConv_ffun_sub_le F φ hφ ff hff fa₀ Φ₀ hfaΦ hfa₀ Ψ₀ hΨs hΨ1 hkill Kc hKcΨ p q hp hq δ hclose g
    rw [ffun_eq_afun Ψ₀ p q ff] at hle
    refine hle.trans ?_
    calc δ * (∫ y, ‖φ (g * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F))
        ≤ δ * (Bst * Ir) := mul_le_mul_of_nonneg_left (hM_le g hg) hδpos.le
      _ ≤ η / (Bst * Ir + 1) * (Bst * Ir) := mul_le_mul_of_nonneg_right hδle₂ hBI0
      _ ≤ η := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith

open scoped Pointwise in

private theorem exists_archFiniteVector_rot {w : InfinitePlace F} (hw : w.IsReal) (nn : ℤ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa₀ : IsArchTestFactor F fa₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ ≠ 0)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (η : ℝ) (hη : 0 < η) :
    ∃ (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∈ archCutSubmodule F tys ∧
        (∀ g ∈ C, ‖rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g -
            rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g‖ ≤ η) ∧
        IsArchTestFactor F (Ws23.SMinf.Rot.rotAvgArch w hw nn fa) ∧
        (∃ tys' : ArchTypeFamily F, IsArchFactorBiFinite F tys' (Ws23.SMinf.Rot.rotAvgArch w hw nn fa) ∧
          rightConv F φ (fun x => Ws23.SMinf.Rot.rotAvgArch w hw nn fa (glArch (𝓞 F) F x) * ff (glFin (𝓞 F) F x)) ∈
            archCutSubmodule F tys') := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  obtain ⟨⟨Φ₀, hΦ₀, hfaΦ⟩, hfa₀c⟩ := id hfa₀
  obtain ⟨Ψ₀, hΨs, hΨ1, hΨinv, hΨinvR, hkill, Kc, hKc, hKcΨ⟩ :=
    ArchFiniteVector.Plateau.exists_plateau F (tsupport fa₀) hfa₀c

  have hΨarch' : IsArchTestFactor F
      (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ)) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill (fun _ => (1 : ℂ)) contDiff_const
  have hr' := continuous_and_hasCompactSupport_tensor F _ hΨarch' ff hff
  have hr_eq' : (fun g => (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
      (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = rfun Ψ₀ ff := by
    funext g
    simp only [rfun, one_mul]
  rw [hr_eq'] at hr'
  obtain ⟨Bφ, hBφ⟩ : ∃ B : ℝ, ∀ z ∈ C * tsupport (rfun Ψ₀ ff), ‖φ z‖ ≤ B :=
    (hC.mul hr'.2).exists_bound_of_continuousOn hφ.continuousOn
  set Bst : ℝ := max Bφ 0 with hBst
  set Ir : ℝ := ∫ y, ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with hIr
  have hIr0 : 0 ≤ Ir := integral_nonneg fun _ => norm_nonneg _
  have hBI0 : 0 ≤ Bst * Ir := mul_nonneg (le_max_right _ _) hIr0
  have hM_le : ∀ g ∈ C, (∫ y, ‖φ (g * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) ≤ Bst * Ir := by
    intro g hg
    have hi1 : Integrable (fun y => ‖φ (g * y)‖ * ‖rfun Ψ₀ ff y‖) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
      simpa only [norm_mul] using
        (ArchFiniteVector.KFinite.integrable_rightConv_integrand F φ hφ _ hr'.1 hr'.2 g).norm
    have hi2 : Integrable (fun y => Bst * ‖rfun Ψ₀ ff y‖) (adelicGLHaar (Fin 2) (𝓞 F) F) :=
      ((hr'.1.norm).integrable_of_hasCompactSupport hr'.2.norm).const_mul Bst
    rw [hIr, ← integral_const_mul]
    refine integral_mono hi1 hi2 fun y => ?_
    by_cases hy : y ∈ tsupport (rfun Ψ₀ ff)
    · exact mul_le_mul_of_nonneg_right ((hBφ _ (Set.mul_mem_mul hg hy)).trans (le_max_left _ _)) (norm_nonneg _)
    · have h0 : rfun Ψ₀ ff y = 0 := by
        by_contra h
        exact hy (subset_tsupport _ h)
      simp only [h0, norm_zero, mul_zero, le_refl]
  obtain ⟨δ₁, hδ₁pos, hsmall₁⟩ : ∃ δ : ℝ, 0 < δ ∧
      δ * (∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) <
        ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖ := by
    set M : ℝ := ∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
    set cc : ℝ := ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖
    have hMnn : 0 ≤ M := integral_nonneg fun y => by positivity
    have hccpos : 0 < cc := norm_pos_iff.mpr hg₀
    have h2 : 0 < 2 * (M + 1) := by linarith
    refine ⟨cc / (2 * (M + 1)), div_pos hccpos h2, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ h2]
    nlinarith
  set δ : ℝ := min δ₁ (η / (Bst * Ir + 1)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos (div_pos hη (by linarith))
  have hδle₁ : δ ≤ δ₁ := min_le_left _ _
  have hδle₂ : δ ≤ η / (Bst * Ir + 1) := min_le_right _ _
  have hsmall : δ * (∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) <
      ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖ :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hδle₁ (integral_nonneg fun y => by positivity)) hsmall₁
  obtain ⟨p, q, hp, hps, hpsep, hq, hqs, hqsep, hclose⟩ :=
    ArchFiniteVector.Poly.exists_poly_pair_near' (E F) Kc hKc Φ₀ hΦ₀.continuous δ hδpos
  obtain ⟨n, bp, hbp, hpspan⟩ := hps.exists_smooth_span hp
  obtain ⟨m, bq, hbq, hqspan⟩ := hqs.exists_smooth_span hq
  have hfarch : IsArchTestFactor F (afun Ψ₀ p q) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_pair F hp hq)
  have hune : rightConv F φ (fun g => afun Ψ₀ p q (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 := fun h0 =>
    rightConv_ffun_ne_zero F φ hφ ff hff fa₀ Φ₀ hfaΦ hfa₀ Ψ₀ hΨs hΨ1 hkill Kc hKcΨ p q hp hq δ hclose g₀ hsmall
      (by rw [ffun_eq_afun Ψ₀ p q ff, h0]; rfl)
  have hfs : ∀ i, Continuous (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i))
      (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i) ∧ HasCompactSupport (Fin.append
        (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i) := by
    have key : ∀ (b : E F → ℝ), ContDiff ℝ (⊤ : ℕ∞) b →
        Continuous (Tfix F (rfun Ψ₀ ff) b) ∧ HasCompactSupport (Tfix F (rfun Ψ₀ ff) b) := by
      intro b hb
      have harch : IsArchTestFactor F (fun z => (fun M => (b M : ℂ)) (archEntries F z) *
          (Ψ₀ (archEntries F z) : ℂ)) :=
        isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_ofReal_comp F hb)
      have h := continuous_and_hasCompactSupport_tensor F _ harch ff hff
      have e : (fun g => (fun z => (fun M => (b M : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
          (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = Tfix F (rfun Ψ₀ ff) b := by
        funext g
        rw [Tfix_apply]
        simp only [rfun]
        ring
      rw [e] at h
      exact h
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact key _ (hbp i)
    · rw [Fin.append_right]
      exact key _ (hbq j)
  have hV : ∀ w : InfinitePlace F, ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ V ∧ rightConv F φ (ffun Ψ₀ p q ff) ∈ V ∧
        ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ v ∈ V, (fun x => v (x * rowIsometryInclAt₀ F w k)) ∈ V :=
    fun w => ArchFiniteVector.KFinite.exists_finiteDimensional_mem_of_forall_mem_span F (rowIsometryInclAt₀ F w) φ
      hφ _ (fun i => (hfs i).1) (fun i => (hfs i).2) (ffun Ψ₀ p q ff)
      (ffun_translate_mem_span Ψ₀ p q ff hΨinv bp bq hpspan hqspan w)
  have hτ₃ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w,
      rightConv F φ (ffun Ψ₀ p q ff) ∈ archTypeSubmoduleAt F w τ := by
    intro w
    obtain ⟨V, hfin, hu, hstab⟩ := hV w
    haveI := hfin
    obtain ⟨n', ρ, hmem⟩ :=
      ArchFiniteVector.ArchCut.exists_rep_mem_typeSubmodule (rowIsometryInclAt₀ F w) V hu hstab
    exact ⟨⟨n', ρ⟩, hmem⟩
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (BA Ψ₀ bp bq))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (BAinv Ψ₀ bp bq))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hτ₂ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w, afun Ψ₀ p q ∈ archFactorDualTypeSubmoduleAt F w τ :=
    fun w => exists_archRepAt_dual_of_translates F w (afun Ψ₀ p q) _
      (fun k => afun_mul_right_mem_span Ψ₀ p q hΨinvR bp bq hpspan hqspan w k)
  have hτ₁ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w,
      (fun x => afun Ψ₀ p q x⁻¹) ∈ archFactorTypeSubmoduleAt F w τ :=
    fun w => exists_archRepAt_of_translates F w (fun x => afun Ψ₀ p q x⁻¹) _
      (fun k => afun_inv_mul_mem_span Ψ₀ p q hΨinv bp bq hpspan hqspan w k)
  choose τ₁ hτ₁ using hτ₁
  choose τ₂ hτ₂ using hτ₂
  choose τ₃ hτ₃ using hτ₃

  set T : (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) → (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
    Ws23.SMinf.Rot.rotAvgArch w hw nn with hTdef
  set TL : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) := Ws23.SMinf.Rot.rotAvgL w hw nn with hTLdef

  set Lfam : ℝ → E F →ₗ[ℝ] E F :=
    fun θ => Lsub F (archEntries F (archGLIncl F w
      ((Ws23.SMinf.Rot.rotAt F hw (Ws23.SMinf.Rot.norm_symm_ringEquivRealOfIsReal F hw) (-θ) :
          rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))) with hLfam
  have hAcont : Continuous fun θ : ℝ => archEntries F (archGLIncl F w
      ((Ws23.SMinf.Rot.rotAt F hw (Ws23.SMinf.Rot.norm_symm_ringEquivRealOfIsReal F hw) (-θ) :
          rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)) := by
    have e : (fun θ : ℝ => archEntries F (archGLIncl F w
        ((Ws23.SMinf.Rot.rotAt F hw (Ws23.SMinf.Rot.norm_symm_ringEquivRealOfIsReal F hw) (-θ) :
          rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))) =
        (archEntries F) ∘ (fun θ : ℝ => glArch (𝓞 F) F (Ws23.SMinf.Rot.archRot w hw θ)) ∘ (fun θ : ℝ => -θ) := by
      funext θ
      simp only [Function.comp_apply]
      rw [Ws23.SMinf.Rot.glArch_archRot]
    rw [e]
    have cG : Continuous (fun θ : ℝ => glArch (𝓞 F) F (Ws23.SMinf.Rot.archRot w hw θ)) :=
      Ws23.SMinf.Rot.continuous_glArch_archRot
    exact (ArchFiniteVector.Plateau.continuous_archEntries F).comp (cG.comp continuous_neg)
  have hL : ∀ v : E F, Continuous fun θ => Lfam θ v := by
    intro v
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [hLfam, Lsub_apply]
    refine continuous_finsetSum _ fun l _ => ?_
    exact (((continuous_apply l).comp ((continuous_apply i).comp hAcont))).mul continuous_const

  have hcexp : Continuous fun θ : ℝ => Complex.exp (-(Complex.I * nn * θ)) := Ws23.SMinf.Rot.continuous_expChar nn
  obtain ⟨Gp, hGp, hGp_eq⟩ := (hpsep Lfam hL).contDiff_average _ hcexp 0 (2 * Real.pi)
  obtain ⟨Gq, hGq, hGq_eq⟩ := (hqsep Lfam hL).contDiff_average _ hcexp 0 (2 * Real.pi)

  have hTfa : T (afun Ψ₀ p q) = fun z => (fun M => Gp M + Gq M * Complex.I) (archEntries F z) *
      (Ψ₀ (archEntries F z) : ℂ) := by
    funext z
    rw [hTdef, Ws23.SMinf.Rot.rotAvgArch_eq_integral_archGLIncl]
    have hint : ∀ θ : ℝ, Complex.exp (-(Complex.I * nn * θ)) * afun Ψ₀ p q (archGLIncl F w
        ((Ws23.SMinf.Rot.rotAt F hw (Ws23.SMinf.Rot.norm_symm_ringEquivRealOfIsReal F hw) (-θ) :
          rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) * z) =
        (Complex.exp (-(Complex.I * nn * θ)) * (p (Lfam θ (archEntries F z)) : ℂ)) * (Ψ₀ (archEntries F z) : ℂ) +
        (Complex.exp (-(Complex.I * nn * θ)) * (q (Lfam θ (archEntries F z)) : ℂ)) *
          (Complex.I * (Ψ₀ (archEntries F z) : ℂ)) := by
      intro θ
      rw [afun_mul_left Ψ₀ p q hΨinv w _ (Ws23.SMinf.Rot.isRowIsometry_rotAt (-θ)) z, TfixA_apply, TfixA_apply]
      simp only [rA, hLfam, Function.comp_apply]
      ring
    simp_rw [hint]
    have hi1 : IntervalIntegrable (fun θ : ℝ => (Complex.exp (-(Complex.I * nn * θ)) *
        (p (Lfam θ (archEntries F z)) : ℂ)) * (Ψ₀ (archEntries F z) : ℂ)) MeasureTheory.volume 0 (2 * Real.pi) :=
      ((hcexp.mul (Complex.continuous_ofReal.comp (hp.continuous.comp (hL _)))).mul continuous_const).intervalIntegrable
        (μ := MeasureTheory.volume) _ _
    have hi2 : IntervalIntegrable (fun θ : ℝ => (Complex.exp (-(Complex.I * nn * θ)) *
        (q (Lfam θ (archEntries F z)) : ℂ)) * (Complex.I * (Ψ₀ (archEntries F z) : ℂ))) MeasureTheory.volume 0 (2 * Real.pi) :=
      ((hcexp.mul (Complex.continuous_ofReal.comp (hq.continuous.comp (hL _)))).mul continuous_const).intervalIntegrable
        (μ := MeasureTheory.volume) _ _
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      hGp_eq, hGq_eq]
    ring
  have hTfarch : IsArchTestFactor F (T (afun Ψ₀ p q)) := by
    rw [hTfa]
    exact isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _
      (hGp.add (hGq.mul contDiff_const))

  have hTadd : ∀ u v : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, Continuous u → Continuous v → T (u + v) = T u + T v :=
    fun u v hu hv => by rw [hTdef]; exact Ws23.SMinf.Rot.rotAvgArch_add nn hu hv
  have hTsmul : ∀ (c : ℂ) (u : GL (Fin 2) (InfiniteAdeleRing F) → ℂ), T (c • u) = c • T u :=
    fun c u => by rw [hTdef]; exact Ws23.SMinf.Rot.rotAvgArch_smul nn c u
  have hTLadd : ∀ u v : AdelicGL2 (𝓞 F) F → ℂ, Continuous u → Continuous v → TL (u + v) = TL u + TL v :=
    fun u v hu hv => by rw [hTLdef]; exact Ws23.SMinf.Rot.rotAvgL_add nn hu hv
  have hTLsmul : ∀ (c : ℂ) (u : AdelicGL2 (𝓞 F) F → ℂ), TL (c • u) = c • TL u :=
    fun c u => by rw [hTLdef]; exact Ws23.SMinf.Rot.rotAvgL_smul nn c u
  have hrAc : Continuous (rA Ψ₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
    Complex.continuous_ofReal.comp (hΨs.continuous.comp (ArchFiniteVector.Plateau.continuous_archEntries F))
  have hBAc : ∀ i, Continuous (BA Ψ₀ bp bq i) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [BA, Fin.append_left]
      show Continuous fun z => ((bp i) (archEntries F z) : ℂ) * rA Ψ₀ z
      exact (Complex.continuous_ofReal.comp ((hbp i).continuous.comp
        (ArchFiniteVector.Plateau.continuous_archEntries F))).mul hrAc
    · simp only [BA, Fin.append_right]
      show Continuous fun z => ((bq j) (archEntries F z) : ℂ) * rA Ψ₀ z
      exact (Complex.continuous_ofReal.comp ((hbq j).continuous.comp
        (ArchFiniteVector.Plateau.continuous_archEntries F))).mul hrAc
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i => T (BA Ψ₀ bp bq i))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i => fun x => T (BA Ψ₀ bp bq i) x⁻¹)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hcommA : ∀ (v : InfinitePlace F) (k : rowIsometrySubgroup₀ v.Completion) (θ : ℝ),
      glArch (𝓞 F) F (Ws23.SMinf.Rot.archRot w hw θ) * archRowIsometryInclAt₀ F v k =
        archRowIsometryInclAt₀ F v k * glArch (𝓞 F) F (Ws23.SMinf.Rot.archRot w hw θ) := by
    intro v k θ
    rw [archRowIsometryInclAt₀_eq]
    exact Ws23.SMinf.Rot.glArch_archRot_mul_archGLIncl v k θ
  have hτ₂' : ∀ v : InfinitePlace F, ∃ τ : ArchRepAt F v, T (afun Ψ₀ p q) ∈ archFactorDualTypeSubmoduleAt F v τ := by
    intro v
    refine exists_archRepAt_dual_of_translates F v (T (afun Ψ₀ p q))
      (Submodule.span ℂ (Set.range fun i => T (BA Ψ₀ bp bq i))) fun k => ?_
    have e : (fun x => T (afun Ψ₀ p q) (x * archRowIsometryInclAt₀ F v k)) =
        T (fun x => afun Ψ₀ p q (x * archRowIsometryInclAt₀ F v k)) := by
      rw [hTdef, Ws23.SMinf.Rot.rotAvgArch_mul_right]
    rw [e]
    exact Ws23.SMinf.Sep.span_image_of_addOn (BA Ψ₀ bp bq) hBAc T hTadd hTsmul
      (afun_mul_right_mem_span Ψ₀ p q hΨinvR bp bq hpspan hqspan v k)
  have hτ₁' : ∀ v : InfinitePlace F, ∃ τ : ArchRepAt F v,
      (fun x => T (afun Ψ₀ p q) x⁻¹) ∈ archFactorTypeSubmoduleAt F v τ := by
    intro v
    refine exists_archRepAt_of_translates F v (fun x => T (afun Ψ₀ p q) x⁻¹)
      (Submodule.span ℂ (Set.range fun i => fun x => T (BA Ψ₀ bp bq i) x⁻¹)) fun k => ?_
    have h1 := afun_mul_left_mem_span Ψ₀ p q hΨinv bp bq hpspan hqspan v k⁻¹
    have h2 := Ws23.SMinf.Sep.span_image_of_addOn (BA Ψ₀ bp bq) hBAc T hTadd hTsmul h1
    have h3 := ArchFiniteVector.ArchCut.comp_inv_mem_span (fun i => T (BA Ψ₀ bp bq i)) h2
    have e : (fun x => (fun x => T (afun Ψ₀ p q) x⁻¹) (x * archRowIsometryInclAt₀ F v k)) =
        fun x => (T (fun z => afun Ψ₀ p q (archRowIsometryInclAt₀ F v k⁻¹ * z))) x⁻¹ := by
      funext x
      have hh := Ws23.SMinf.Rot.rotAvgArch_inv_mul_of_commute nn (afun Ψ₀ p q) (h := archRowIsometryInclAt₀ F v k)
        (fun θ => hcommA v k θ)
      simp only [_root_.mul_inv_rev, map_inv]
      rw [hTdef, hh]
    rw [e]
    exact h3

  set f₁ : AdelicGL2 (𝓞 F) F → ℂ := fun x => T (afun Ψ₀ p q) (glArch (𝓞 F) F x) * ff (glFin (𝓞 F) F x) with hf₁
  have hf₁TL : f₁ = TL (ffun Ψ₀ p q ff) := by
    rw [hf₁, hTLdef, hTdef, ffun_eq_afun, Ws23.SMinf.Rot.rotAvgL_tensor]
  have hfs' : ∀ i, Continuous (TL (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i))
      (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i)) ∧ HasCompactSupport (TL (Fin.append
        (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i)) := fun i =>
    ⟨by rw [hTLdef]; exact Ws23.SMinf.Rot.continuous_rotAvgL nn (hfs i).1,
     by rw [hTLdef]; exact Ws23.SMinf.Rot.hasCompactSupport_rotAvgL nn (hfs i).2⟩
  have hV' : ∀ v : InfinitePlace F, ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ V ∧ rightConv F φ f₁ ∈ V ∧
        ∀ k : rowIsometrySubgroup₀ v.Completion, ∀ u ∈ V, (fun x => u (x * rowIsometryInclAt₀ F v k)) ∈ V := by
    intro v
    refine ArchFiniteVector.KFinite.exists_finiteDimensional_mem_of_forall_mem_span F (rowIsometryInclAt₀ F v) φ
      hφ _ (fun i => (hfs' i).1) (fun i => (hfs' i).2) f₁ fun k => ?_
    have e : (fun y => f₁ ((rowIsometryInclAt₀ F v k)⁻¹ * y)) =
        TL (fun y => ffun Ψ₀ p q ff ((rowIsometryInclAt₀ F v k)⁻¹ * y)) := by
      rw [hf₁TL, hTLdef, Ws23.SMinf.Rot.rotAvgL_comp_mul_left_of_commute nn _
        (fun θ => Ws23.SMinf.Rot.archRot_mul_rowIsometryInclAt₀ v k θ)]
    rw [e]
    exact Ws23.SMinf.Sep.span_image_of_addOn _ (fun i => (hfs i).1) TL hTLadd hTLsmul
      (ffun_translate_mem_span Ψ₀ p q ff hΨinv bp bq hpspan hqspan v k)
  have hτ₃' : ∀ v : InfinitePlace F, ∃ τ : ArchRepAt F v, rightConv F φ f₁ ∈ archTypeSubmoduleAt F v τ := by
    intro v
    obtain ⟨V, hfin, hu, hstab⟩ := hV' v
    haveI := hfin
    obtain ⟨n', ρ, hmem⟩ :=
      ArchFiniteVector.ArchCut.exists_rep_mem_typeSubmodule (rowIsometryInclAt₀ F v) V hu hstab
    exact ⟨⟨n', ρ⟩, hmem⟩
  choose τ₁' hτ₁' using hτ₁'
  choose τ₂' hτ₂' using hτ₂'
  choose τ₃' hτ₃' using hτ₃'
  refine ⟨tripleFamily F τ₁ τ₂ τ₃, afun Ψ₀ p q, hfarch,
    ⟨mem_archFactorCut_tripleFamily F τ₁ τ₂ τ₃ hτ₁, mem_archFactorDualCut_tripleFamily F τ₁ τ₂ τ₃ hτ₂⟩, hune, ?_, ?_,
    hTfarch, ⟨tripleFamily F τ₁' τ₂' τ₃',
      ⟨mem_archFactorCut_tripleFamily F τ₁' τ₂' τ₃' hτ₁', mem_archFactorDualCut_tripleFamily F τ₁' τ₂' τ₃' hτ₂'⟩,
      mem_archCut_tripleFamily F τ₁' τ₂' τ₃' hτ₃'⟩⟩
  · have h3 := mem_archCut_tripleFamily F τ₁ τ₂ τ₃ hτ₃
    rwa [ffun_eq_afun] at h3
  · intro g hg
    have hle := rightConv_ffun_sub_le F φ hφ ff hff fa₀ Φ₀ hfaΦ hfa₀ Ψ₀ hΨs hΨ1 hkill Kc hKcΨ p q hp hq δ hclose g
    rw [ffun_eq_afun Ψ₀ p q ff] at hle
    refine hle.trans ?_
    calc δ * (∫ y, ‖φ (g * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F))
        ≤ δ * (Bst * Ir) := mul_le_mul_of_nonneg_left (hM_le g hg) hδpos.le
      _ ≤ η / (Bst * Ir + 1) * (Bst * Ir) := mul_le_mul_of_nonneg_right hδle₂ hBI0
      _ ≤ η := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith

end BiFinite
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

end ArchFiniteVector.Assembly
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

end ModAssembly
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

section A2export
open NumberField NumberField.InfinitePlace NumberField.AdelicLevel AutomorphicForm IsDedekindDomain
theorem Ws23.SMinf.exists_archFiniteVector_uniformOn_rotAvgArch (F : Type) [Field F] [NumberField F]
    {w : InfinitePlace F} (hw : w.IsReal) (n : ℤ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa₀ : IsArchTestFactor F fa₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ ≠ 0)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (η : ℝ) (hη : 0 < η) :
    ∃ (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∈ archCutSubmodule F tys ∧
        (∀ g ∈ C, ‖rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g -
            rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g‖ ≤ η) ∧
        IsArchTestFactor F (Ws23.SMinf.Rot.rotAvgArch w hw n fa) ∧
        (∃ tys' : ArchTypeFamily F, IsArchFactorBiFinite F tys' (Ws23.SMinf.Rot.rotAvgArch w hw n fa) ∧
          rightConv F φ (fun x => Ws23.SMinf.Rot.rotAvgArch w hw n fa (glArch (𝓞 F) F x) * ff (glFin (𝓞 F) F x)) ∈
            archCutSubmodule F tys') :=
  ArchFiniteVector.Assembly.exists_archFiniteVector_rot F hw n φ hφ fa₀ hfa₀ ff hff g₀ hg₀ C hC η hη
end A2export
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

section ModConvHalfR

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

namespace G1PrimeRat
namespace ConvHalf

variable (F : Type) [Field F] [NumberField F]

private theorem exists_ne_zero_of_rightConv_ne_zero (φ f : AdelicGL2 (𝓞 F) F → ℂ) (h : ∃ g, rightConv F φ f g ≠ 0) :
    ∃ y, f y ≠ 0 := by
  obtain ⟨g, hg⟩ := h
  by_contra hcon
  refine hg ?_
  have hf : f = fun _ => 0 := funext fun y => Classical.by_contradiction fun hy => hcon ⟨y, hy⟩
  rw [hf, rightConv_zero_right]

private theorem support_shape_of_finFactor (N : Ideal (𝓞 F)) (f₀ : AdelicGL2 (𝓞 F) F → ℂ)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hf₀ : ∀ g, f₀ g = fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) (hne : ∃ y₀, f₀ y₀ ≠ 0)
    (hsupp : ∀ x, f₀ x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hf : ∀ g, f g = fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) :
    ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k := by
  intro x hx
  obtain ⟨y₀, hy₀⟩ := hne
  have hffx : ff (glFin (𝓞 F) F x) ≠ 0 := fun h => hx (by rw [hf x, h, mul_zero])
  have hfa₀ : fa₀ (glArch (𝓞 F) F y₀) ≠ 0 := fun h => hy₀ (by rw [hf₀ y₀, h, zero_mul])
  have hyA : glArch (𝓞 F) F
      (adelicArchGLIncl F (glArch (𝓞 F) F y₀) * (adelicArchGLIncl F (glArch (𝓞 F) F x))⁻¹ * x)
        = glArch (𝓞 F) F y₀ := by
    simp only [map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel_right]
  have hyF : glFin (𝓞 F) F
      (adelicArchGLIncl F (glArch (𝓞 F) F y₀) * (adelicArchGLIncl F (glArch (𝓞 F) F x))⁻¹ * x)
        = glFin (𝓞 F) F x := by
    simp only [map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]
  have hy : f₀ (adelicArchGLIncl F (glArch (𝓞 F) F y₀) * (adelicArchGLIncl F (glArch (𝓞 F) F x))⁻¹ * x) ≠ 0 := by
    rw [hf₀, hyA, hyF]
    exact mul_ne_zero hfa₀ hffx
  obtain ⟨a', k, ha', hk, hyk⟩ := hsupp _ hy
  refine ⟨adelicArchGLIncl F (glArch (𝓞 F) F x) * (adelicArchGLIncl F (glArch (𝓞 F) F y₀))⁻¹ * a', k, ?_, hk, ?_⟩
  · simp only [map_mul, map_inv, glFin_adelicArchGLIncl, ha', inv_one, mul_one]
  · rw [mul_assoc, ← hyk]
    group

private theorem isIsotypicCuspFormAt_rightConv_of_memLp (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k)
    (hmem : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      MemLp (rightConv F R.toFun f) 2
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))) :
    IsIsotypicCuspFormAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      R.centralChar Φ.level R.exceptionalSet Φ (rightConv F R.toFun f) := by
  obtain ⟨hcusp, hkf, hlev, hhecke⟩ :=
    AutomorphicForm.isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
      F c u d₁ d₂ T Φ.toRawCentral R hR f hf hfs
  have hcont : Continuous (rightConv F R.toFun f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F R.toFun hR f hf).1
  have hauto : IsAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      R.centralChar R.toFun := R.smoothCusp.1.1
  have hlsxi : IsLsXiFunction (𝓞 F) F ⊤ R.centralChar R.toFun :=
    ((@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ (glBorel (Fin 2) (𝓞 F) F) (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ R.centralChar
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) R.toFun).mp hauto).1
  have hauto' : IsAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      R.centralChar (rightConv F R.toFun f) :=
    (@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ (glBorel (Fin 2) (𝓞 F) F) (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ R.centralChar
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (rightConv F R.toFun f)).mpr
      ⟨SmwShell.isLsXiFunction_rightConv_of_isLsXiFunction F ⊤ R.centralChar hlsxi f, hmem⟩
  exact ⟨⟨⟨hauto', hcusp⟩, hkf⟩, hcont, hlev, hhecke,
    fun v hv g => SmwShell.rightConv_mul_left_of_forall_mul F (fun x => R.central_eigen v hv x) g⟩

private theorem exists_finFactor_forall_isIsotypicCuspFormAt_rightConv (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      Φ.toRawCentral)
    (hR : Continuous R.toFun)
    (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (hf₀ : IsFactorizableTestFn F f₀) (hne : ∃ y₀, f₀ y₀ ≠ 0)
    (hsupp : ∀ x, f₀ x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k) :
    ∃ (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
      IsArchTestFactor F fa₀ ∧ IsFinTestFactor F ff ∧
        (∀ g, f₀ g = fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∧
        ∀ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchTestFactor F fa →
          IsIsotypicCuspFormAt F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
            R.centralChar Φ.level R.exceptionalSet Φ
            (rightConv F R.toFun (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g))) := by
  obtain ⟨fa₀, ff, hfa₀, hff, hf₀eq⟩ := hf₀
  refine ⟨fa₀, ff, hfa₀, hff, hf₀eq, fun fa hfa => ?_⟩
  have hf : IsFactorizableTestFn F (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) :=
    ArchFiniteVector.ConvHalf.isFactorizableTestFn_mk F fa hfa ff hff
  have hfs := support_shape_of_finFactor F Φ.level f₀ fa₀ ff hf₀eq hne hsupp _ fa (fun _ => rfl)
  exact isIsotypicCuspFormAt_rightConv_of_memLp F c u d₁ d₂ T Φ R hR _ hf hfs
    (SmwShell.memLp_rightConv_of_lt F c u d₁ d₂ T hd hc hd₁ hcov R.centralChar R.toFun R.smoothCusp hR _ hf)

end G1PrimeRat.ConvHalf
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

end ModConvHalfR
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

section SMinf_reg

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

namespace Ws23
namespace SMinf

variable (F : Type) [Field F] [NumberField F]

theorem rightConv_mul_left_of_forall' {φ f : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F}
    (hφ : ∀ x, φ (h * x) = φ x) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (h * g) = rightConv F φ f g := by
  rw [← rightConv_comp_mul_left]
  simp only [hφ]

theorem rightConv_mul_left_of_forall_mul' {φ f : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F}
    {c : ℂ} (hφ : ∀ x, φ (h * x) = c * φ x) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (h * g) = c * rightConv F φ f g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  rw [← rightConv_comp_mul_left, rightConv_apply, rightConv_apply]
  simp only [hφ, mul_assoc]
  exact MeasureTheory.integral_const_mul _ _

theorem isLsXiFunction_rightConv' (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    IsLsXiFunction (𝓞 F) F Z ξ (rightConv F φ f) where
  left_invariant γ g := rightConv_mul_left_of_forall' F (fun x => hφ.left_invariant γ x) g
  central_transform z g := rightConv_mul_left_of_forall_mul' F (fun x => hφ.central_transform z x) g

theorem exists_foldr_archDerivAt_rightConv_eq {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    ∀ l : List ArchDir, ∃ fl : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F fl ∧
      l.foldr (archDerivAt hw) (rightConv F φ f) = rightConv F φ fl := by
  intro l
  induction l with
  | nil => exact ⟨f, hf, rfl⟩
  | cons d l ih =>
    obtain ⟨fl, hfl, hEq⟩ := ih
    obtain ⟨fa, ff, hfa, hff, hfl_eq⟩ := hfl
    have hder := AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d
    obtain ⟨fa', hfa', hderiv⟩ := hder.2.1 fa ff hfa
    refine ⟨fun y => fa' (glArch (𝓞 F) F y) * ff (glFin (𝓞 F) F y), ⟨fa', ff, hfa', hff, fun _ => rfl⟩, ?_⟩
    rw [List.foldr_cons, hEq, (hder.1 φ fl hφc ⟨fa, ff, hfa, hff, hfl_eq⟩).2, ← hderiv]
    congr 1
    funext y
    simp only [hfl_eq]

theorem reg (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hφc : Continuous φ) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    {w : InfinitePlace F} (hw : w.IsReal) :
    ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) (rightConv F φ f)) ∧
      ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
          ‖l.foldr (archDerivAt hw) (rightConv F φ f) g‖ ≤ B := by
  intro l
  obtain ⟨fl, hfl, hEq⟩ := exists_foldr_archDerivAt_rightConv_eq F hw φ hφc f hf l
  rw [hEq]
  refine ⟨(AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hφc fl hfl).1, fun e₁ e₂ he₁ he => ?_⟩
  obtain ⟨C, hC⟩ := AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre F c u d₁ d₂ T hc hd₁ hd hcov ξ fl hfl
  have hwin := hC φ hφ hφc
  obtain ⟨N, hN⟩ := AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T hd hcov e₁ e₂ he₁
  have hlsxi : IsLsXiFunction (𝓞 F) F ⊤ ξ φ :=
    ((@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ (glBorel (Fin 2) (𝓞 F) F) (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) φ).mp hφ.1.1).1
  have hconv : IsLsXiFunction (𝓞 F) F ⊤ ξ (rightConv F φ fl) := isLsXiFunction_rightConv' F ⊤ ξ hlsxi fl
  set K0 : ℝ := max (C * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
                (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))).toReal) 0 with hK0
  have hK0nn : 0 ≤ K0 := le_max_right _ _
  refine ⟨K0 * ∑ n ∈ N, ‖((ξ ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)‖, fun g hg => ?_⟩
  obtain ⟨γ, n, hn, x, hx, s, hs, hsx⟩ := hN g hg
  have hsx' : s * (centralScalar (𝓞 F) F n * x) = globalPoints (𝓞 F) F γ * g := hsx
  have hkey : globalPoints (𝓞 F) F γ * g = centralScalar (𝓞 F) F n * (s * x) := by
    rw [← hsx', ← mul_assoc, mul_centralScalar_comm, mul_assoc]
  have h1 : rightConv F φ fl g = rightConv F φ fl (globalPoints (𝓞 F) F γ * g) := (hconv.left_invariant γ g).symm
  have h2 : rightConv F φ fl (centralScalar (𝓞 F) F n * (s * x)) =
      ((ξ ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ) * rightConv F φ fl (s * x) :=
    hconv.central_transform ⟨n, Subgroup.mem_top n⟩ (s * x)
  have hmem : s * x ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) :=
    Set.mem_iUnion₂.mpr ⟨x, hx, s, hs, rfl⟩
  have h3 : ‖rightConv F φ fl (s * x)‖ ≤ K0 := (hwin (s * x) hmem).trans (le_max_left _ _)
  rw [h1, hkey, h2, norm_mul]
  calc ‖((ξ ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)‖ * ‖rightConv F φ fl (s * x)‖
      ≤ ‖((ξ ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)‖ * K0 := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ ≤ (∑ m ∈ N, ‖((ξ ⟨m, Subgroup.mem_top m⟩ : ℂˣ) : ℂ)‖) * K0 :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun m => ‖((ξ ⟨m, Subgroup.mem_top m⟩ : ℂˣ) : ℂ)‖)
          (fun _ _ => norm_nonneg _) hn) hK0nn
    _ = K0 * ∑ m ∈ N, ‖((ξ ⟨m, Subgroup.mem_top m⟩ : ℂˣ) : ℂ)‖ := mul_comm _ _

end Ws23.SMinf
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

end SMinf_reg
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

end
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

open NumberField NumberField.AdelicLevel
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
p2m_open "NumberField.InfiniteAdeleRing AutomorphicForm Metric Topology MeasureTheory"

open scoped Classical

noncomputable section

namespace TestFnNearIdentity

variable (F : Type) [Field F] [NumberField F]

private abbrev E : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

private def ofE (m : E F) : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F) := m

omit [NumberField F] in
private theorem continuous_ringEquiv_mixedSpace : Continuous (ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

omit [NumberField F] in
private theorem continuous_ringEquiv_mixedSpace_symm : Continuous (ringEquiv_mixedSpace F).symm := by
  apply continuous_pi
  intro v
  by_cases hv : IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace F => (ringEquiv_mixedSpace F).symm y v)
        = fun y => (isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      have h := congrArg (fun z : mixedEmbedding.mixedSpace F => z.1 ⟨v, hv⟩)
        ((ringEquiv_mixedSpace F).apply_symm_apply y)
      exact h
    rw [key]
    exact (isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : IsComplex v := not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace F => (ringEquiv_mixedSpace F).symm y v)
        = fun y => (isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨v, hc⟩) := by
      funext y
      apply (isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      have h := congrArg (fun z : mixedEmbedding.mixedSpace F => z.2 ⟨v, hc⟩)
        ((ringEquiv_mixedSpace F).apply_symm_apply y)
      exact h
    rw [key]
    exact (isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

private def mixedHomeo : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F where
  toEquiv := (ringEquiv_mixedSpace F).toEquiv
  continuous_toFun := continuous_ringEquiv_mixedSpace F
  continuous_invFun := continuous_ringEquiv_mixedSpace_symm F

private def matHomeo : (Fin 2 → Fin 2 → InfiniteAdeleRing F) ≃ₜ E F :=
  Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => mixedHomeo F

private def pairHomeo :
    (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) × (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))ᵐᵒᵖ)
      ≃ₜ (E F × E F) :=
  Homeomorph.prodCongr (matHomeo F) (MulOpposite.opHomeomorph.symm.trans (matHomeo F))

private def J (g : GL (Fin 2) (InfiniteAdeleRing F)) : E F × E F :=
  pairHomeo F (Units.embedProduct _ g)

omit [NumberField F] in
private theorem J_apply (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    J F g = (archEntries F g, archEntries F g⁻¹) := rfl

omit [NumberField F] in
private theorem isClosedEmbedding_J : IsClosedEmbedding (J F) :=
  (pairHomeo F).isClosedEmbedding.comp Units.isClosedEmbedding_embedProduct

private def cE : E F := archEntries F 1

omit [NumberField F] in
private theorem ofE_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    ofE F (archEntries F g)
      = (ringEquiv_mixedSpace F).toRingHom.mapMatrix (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  funext i j
  rfl

omit [NumberField F] in
private theorem continuous_detE : Continuous fun m : E F => (ofE F m).det :=
  Continuous.matrix_det continuous_id

private theorem isOpen_detUnit : IsOpen {m : E F | IsUnit (ofE F m).det} :=
  Units.isOpen.preimage (continuous_detE F)

omit [NumberField F] in
private theorem det_cE : (ofE F (cE F)).det = 1 := by
  rw [cE, ofE_archEntries, ← RingHom.map_det, Units.val_one, Matrix.det_one, map_one]

private theorem exists_ball_subset_detUnit :
    ∃ ε > 0, ball (cE F) ε ⊆ {m : E F | IsUnit (ofE F m).det} :=
  Metric.isOpen_iff.1 (isOpen_detUnit F) (cE F) (by simp [det_cE])

private def ε : ℝ := Classical.choose (exists_ball_subset_detUnit F)

private theorem ε_pos : 0 < ε F := (Classical.choose_spec (exists_ball_subset_detUnit F)).1

private theorem ball_ε_subset : ball (cE F) (ε F) ⊆ {m : E F | IsUnit (ofE F m).det} :=
  (Classical.choose_spec (exists_ball_subset_detUnit F)).2

private def Ψ (m : E F) : E F := fun i j => (Ring.inverse (ofE F m).det • (ofE F m).adjugate) i j

private theorem continuousOn_Ψ : ContinuousOn (Ψ F) (closedBall (cE F) (ε F / 2)) := by
  intro m hm
  have hunit : IsUnit (ofE F m).det :=
    ball_ε_subset F (closedBall_subset_ball (by linarith [ε_pos F]) hm)
  obtain ⟨u, hu⟩ := hunit
  apply ContinuousAt.continuousWithinAt
  have h1 : ContinuousAt (fun m : E F => Ring.inverse (ofE F m).det) m := by
    have hi : ContinuousAt Ring.inverse (ofE F m).det := hu ▸ NormedRing.inverse_continuousAt u
    exact hi.comp (continuous_detE F).continuousAt
  have h2 : Continuous fun m : E F => (ofE F m).adjugate := Continuous.matrix_adjugate continuous_id
  have h3 : ContinuousAt (fun m : E F =>
      (Ring.inverse (ofE F m).det • (ofE F m).adjugate :
        Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) m :=
    h1.smul h2.continuousAt
  exact h3

private theorem exists_R : ∃ R > 0, Ψ F '' closedBall (cE F) (ε F / 2) ⊆ closedBall (cE F) R := by
  have hc : IsCompact (Ψ F '' closedBall (cE F) (ε F / 2)) :=
    (isCompact_closedBall _ _).image_of_continuousOn (continuousOn_Ψ F)
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (cE F)
  exact ⟨max R 1, by positivity, hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩

private def R : ℝ := Classical.choose (exists_R F)

private theorem R_pos : 0 < R F := (Classical.choose_spec (exists_R F)).1

private theorem Ψ_subset : Ψ F '' closedBall (cE F) (ε F / 2) ⊆ closedBall (cE F) (R F) :=
  (Classical.choose_spec (exists_R F)).2

private def bump₂ : ContDiffBump (cE F) where
  rIn := R F
  rOut := R F + 1
  rIn_pos := R_pos F
  rIn_lt_rOut := by linarith

private theorem archEntries_inv_mem (g : GL (Fin 2) (InfiniteAdeleRing F))
    (hg : archEntries F g ∈ closedBall (cE F) (ε F / 2)) :
    archEntries F g⁻¹ ∈ closedBall (cE F) (R F) := by
  apply Ψ_subset F
  refine ⟨archEntries F g, hg, ?_⟩

  set A := (ringEquiv_mixedSpace F).toRingHom.mapMatrix
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hA
  have hAinv : (ringEquiv_mixedSpace F).toRingHom.mapMatrix
      ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = A⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [hA, ← map_mul, Units.inv_mul, map_one]
  funext i j
  show (Ring.inverse (ofE F (archEntries F g)).det • (ofE F (archEntries F g)).adjugate) i j
    = archEntries F g⁻¹ i j
  have h2 : archEntries F g⁻¹ i j = (ofE F (archEntries F g⁻¹)) i j := rfl
  rw [h2, ofE_archEntries, ofE_archEntries, hAinv, Matrix.inv_def]

omit [NumberField F] in
private theorem Ψ_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Ψ F (archEntries F g) = archEntries F g⁻¹ := by
  set A := (ringEquiv_mixedSpace F).toRingHom.mapMatrix
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hA
  have hAinv : (ringEquiv_mixedSpace F).toRingHom.mapMatrix
      ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = A⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [hA, ← map_mul, Units.inv_mul, map_one]
  funext i j
  show (Ring.inverse (ofE F (archEntries F g)).det • (ofE F (archEntries F g)).adjugate) i j
    = archEntries F g⁻¹ i j
  have h2 : archEntries F g⁻¹ i j = (ofE F (archEntries F g⁻¹)) i j := rfl
  rw [h2, ofE_archEntries, ofE_archEntries, hAinv, Matrix.inv_def]

private theorem continuousAt_Ψ : ContinuousAt (Ψ F) (cE F) :=
  (continuousOn_Ψ F).continuousAt (closedBall_mem_nhds _ (half_pos (ε_pos F)))

private theorem exists_radius {T : Set (GL (Fin 2) (InfiniteAdeleRing F))}
    (hT : T ∈ 𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε F / 2 ∧ ∀ g, dist (archEntries F g) (cE F) < ρ → g ∈ T := by
  have hJ : J F = (fun m : E F => (m, Ψ F m)) ∘ archEntries F := by
    funext g
    rw [Function.comp_apply, J_apply, Ψ_archEntries]
  have hJ1 : J F 1 = (cE F, Ψ F (cE F)) := by
    show J F 1 = (archEntries F 1, Ψ F (archEntries F 1))
    rw [J_apply, inv_one, Ψ_archEntries F 1, inv_one]
  have hcont : ContinuousAt (fun m : E F => (m, Ψ F m)) (cE F) :=
    continuousAt_id.prodMk (continuousAt_Ψ F)
  have h1 : Filter.Tendsto (fun m : E F => (m, Ψ F m)) (𝓝 (cE F)) (𝓝 (J F 1)) := by
    rw [hJ1]
    exact hcont
  have hle : Filter.comap (archEntries F) (𝓝 (cE F)) ≤ 𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)) :=
    calc Filter.comap (archEntries F) (𝓝 (cE F))
        ≤ Filter.comap (archEntries F)
            (Filter.comap (fun m : E F => (m, Ψ F m)) (𝓝 (J F 1))) :=
          Filter.comap_mono (Filter.tendsto_iff_comap.1 h1)
      _ = Filter.comap (J F) (𝓝 (J F 1)) := by rw [Filter.comap_comap, hJ]
      _ = 𝓝 1 := ((isClosedEmbedding_J F).isInducing.nhds_eq_comap 1).symm
  obtain ⟨S, hS, hST⟩ := Filter.mem_comap.1 (hle hT)
  obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhds_iff.1 hS
  refine ⟨min δ (ε F / 2), lt_min hδ (half_pos (ε_pos F)), min_le_right _ _, fun g hg => ?_⟩
  exact hST (show g ∈ archEntries F ⁻¹' S from
    hδS (Metric.mem_ball.2 (lt_of_lt_of_le hg (min_le_left _ _))))

private theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
      (((k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
      ((((k⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F)
    exact (Units.continuous_coe_inv.matrix_elem i j).prodMk continuous_const

private theorem exists_radius_of_continuous (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε F / 2 ∧ ∀ m : GL (Fin 2) (InfiniteAdeleRing F),
      dist (archEntries F m) (cE F) < ρ →
        ‖φ (g₀ * adelicArchGLIncl F m) - φ g₀‖ ≤ ‖φ g₀‖ / 2 := by
  have hψ : Continuous fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
      φ (g₀ * adelicArchGLIncl F m) - φ g₀ :=
    (hφ.comp (continuous_const.mul (continuous_adelicArchGLIncl F))).sub continuous_const
  have h0 : φ (g₀ * adelicArchGLIncl F 1) - φ g₀ = 0 := by
    rw [map_one, mul_one, sub_self]
  have hT : {m : GL (Fin 2) (InfiniteAdeleRing F) |
      ‖φ (g₀ * adelicArchGLIncl F m) - φ g₀‖ ≤ ‖φ g₀‖ / 2} ∈
        𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)) := by
    have hpre := (hψ.continuousAt (x := (1 : GL (Fin 2) (InfiniteAdeleRing F)))).preimage_mem_nhds
      (closedBall_mem_nhds (φ (g₀ * adelicArchGLIncl F 1) - φ g₀) (half_pos (norm_pos_iff.2 hg₀)))
    rw [h0] at hpre
    exact Filter.mem_of_superset hpre fun m hm =>
      mem_closedBall_zero_iff.1 (Set.mem_preimage.1 hm)
  obtain ⟨ρ, hρ, hρε, h⟩ := exists_radius F hT
  exact ⟨ρ, hρ, hρε, fun m hm => h m hm⟩

private def bumpAt (ρ : ℝ) (hρ : 0 < ρ) : ContDiffBump (cE F) where
  rIn := ρ / 2
  rOut := ρ
  rIn_pos := half_pos hρ
  rIn_lt_rOut := half_lt_self hρ

private def Φ₂ (ρ : ℝ) (hρ : 0 < ρ) (p : E F × E F) : ℂ :=
  (((bumpAt F ρ hρ).toFun p.1 : ℝ) : ℂ) * (((bump₂ F).toFun p.2 : ℝ) : ℂ)

private theorem hasCompactSupport_Φ₂ (ρ : ℝ) (hρ : 0 < ρ) : HasCompactSupport (Φ₂ F ρ hρ) := by
  refine HasCompactSupport.intro'
    ((isCompact_closedBall (cE F) (bumpAt F ρ hρ).rOut).prod
      (isCompact_closedBall (cE F) (bump₂ F).rOut))
    (isClosed_closedBall.prod isClosed_closedBall) fun p hp => ?_
  rw [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · have h' : (bumpAt F ρ hρ).toFun p.1 = 0 :=
      (bumpAt F ρ hρ).zero_of_le_dist (le_of_lt (by rwa [mem_closedBall, not_le] at h))
    simp [Φ₂, h']
  · have h' : (bump₂ F).toFun p.2 = 0 :=
      (bump₂ F).zero_of_le_dist (le_of_lt (by rwa [mem_closedBall, not_le] at h))
    simp [Φ₂, h']

private def fa (ρ : ℝ) (hρ : 0 < ρ) : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := Φ₂ F ρ hρ ∘ J F

private theorem fa_apply (ρ : ℝ) (hρ : 0 < ρ) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    fa F ρ hρ g = (((bumpAt F ρ hρ).toFun (archEntries F g) : ℝ) : ℂ) *
      (((bump₂ F).toFun (archEntries F g⁻¹) : ℝ) : ℂ) := rfl

private theorem fa_eq (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ ε F / 2) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    fa F ρ hρ g = (((bumpAt F ρ hρ).toFun (archEntries F g) : ℝ) : ℂ) := by
  rw [fa_apply]
  by_cases h : archEntries F g ∈ closedBall (cE F) (ε F / 2)
  · rw [(bump₂ F).one_of_mem_closedBall (archEntries_inv_mem F g h), Complex.ofReal_one, mul_one]
  · have h0 : (bumpAt F ρ hρ).toFun (archEntries F g) = 0 := by
      apply (bumpAt F ρ hρ).zero_of_le_dist
      rw [mem_closedBall, not_le] at h
      exact le_of_lt (lt_of_le_of_lt hρε h)
    rw [h0, Complex.ofReal_zero, zero_mul]

private theorem isArchTestFactor_fa (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ ε F / 2) :
    IsArchTestFactor F (fa F ρ hρ) := by
  refine ⟨⟨fun m => (((bumpAt F ρ hρ).toFun m : ℝ) : ℂ), ?_, fun g => fa_eq F ρ hρ hρε g⟩, ?_⟩
  · have hc : (fun m : E F => (((bumpAt F ρ hρ).toFun m : ℝ) : ℂ))
        = Complex.ofRealCLM ∘ (bumpAt F ρ hρ).toFun := by
      funext m
      simp
    rw [hc]
    exact Complex.ofRealCLM.contDiff.comp (bumpAt F ρ hρ).contDiff
  · exact (hasCompactSupport_Φ₂ F ρ hρ).comp_isClosedEmbedding (isClosedEmbedding_J F)

private def Kf (N : Ideal (𝓞 F)) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  (AdelicLevel.finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))

private def ff (N : Ideal (𝓞 F)) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Kf F N).indicator fun _ => 1

private theorem isOpen_Kf {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsOpen (Kf F N) :=
  AdelicLevel.isOpen_finiteLevelOne (𝓞 F) F hN

private theorem isClosed_Kf (N : Ideal (𝓞 F)) : IsClosed (Kf F N) :=
  AdelicLevel.isClosed_finiteLevelOne (𝓞 F) F N

private theorem isCompact_Kf (N : Ideal (𝓞 F)) : IsCompact (Kf F N) :=
  AdelicLevel.isCompact_finiteLevelOne (𝓞 F) F N

private theorem isFinTestFactor_ff {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsFinTestFactor F (ff F N) := by
  refine ⟨?_, HasCompactSupport.intro' (isCompact_Kf F N) (isClosed_Kf F N)
    fun x hx => Set.indicator_of_notMem hx _⟩
  intro s
  have hpre : ff F N ⁻¹' s
      = (if (1 : ℂ) ∈ s then Kf F N else ∅) ∪ (if (0 : ℂ) ∈ s then (Kf F N)ᶜ else ∅) := by
    ext x
    by_cases hx : x ∈ Kf F N <;> by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s <;>
      simp [ff, Set.indicator, hx, h1, h0]
  rw [hpre]
  refine IsOpen.union ?_ ?_
  · split_ifs
    · exact isOpen_Kf F hN
    · exact isOpen_empty
  · split_ifs
    · exact (isClosed_Kf F N).isOpen_compl
    · exact isOpen_empty

private theorem ff_mul_of_mem (N : Ideal (𝓞 F)) {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hk : k ∈ AdelicLevel.finiteLevelOne (𝓞 F) F N) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ff F N (k * x) = ff F N x := by
  by_cases hx : x ∈ Kf F N
  · have hx' : x ∈ AdelicLevel.finiteLevelOne (𝓞 F) F N := hx
    have hkx : k * x ∈ Kf F N := mul_mem hk hx'
    simp only [ff, Set.indicator_of_mem hx, Set.indicator_of_mem hkx]
  · have hkx : k * x ∉ Kf F N := fun h =>
      hx ((Subgroup.mul_mem_cancel_left (AdelicLevel.finiteLevelOne (𝓞 F) F N) hk).1
        (show k * x ∈ AdelicLevel.finiteLevelOne (𝓞 F) F N from h))
    simp only [ff, Set.indicator_of_notMem hx, Set.indicator_of_notMem hkx]

private def testFn (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
  fa F ρ hρ (AdelicLevel.glArch (𝓞 F) F g) * ff F N (AdelicLevel.glFin (𝓞 F) F g)

private def testFnR (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) : AdelicGL2 (𝓞 F) F → ℝ := fun g =>
  (bumpAt F ρ hρ).toFun (archEntries F (AdelicLevel.glArch (𝓞 F) F g)) *
    (Kf F N).indicator (fun _ => (1 : ℝ)) (AdelicLevel.glFin (𝓞 F) F g)

private theorem isFactorizableTestFn_testFn (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ ε F / 2)
    {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsFactorizableTestFn F (testFn F ρ hρ N) :=
  ⟨fa F ρ hρ, ff F N, isArchTestFactor_fa F ρ hρ hρε, isFinTestFactor_ff F hN, fun _ => rfl⟩

private theorem testFn_mul_of_mem (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (x : AdelicGL2 (𝓞 F) F) :
    testFn F ρ hρ N (k * x) = testFn F ρ hρ N x := by
  obtain ⟨hk₁, hk₂⟩ := Subgroup.mem_inf.1 hk
  have h1 : AdelicLevel.glArch (𝓞 F) F k = 1 := (mem_finiteAdelicGL2Subgroup_iff F k).1 hk₂
  have h2 : AdelicLevel.glFin (𝓞 F) F k ∈ AdelicLevel.finiteLevelOne (𝓞 F) F N :=
    AdelicLevel.mem_levelOne_iff.1 hk₁
  simp only [testFn, map_mul, h1, one_mul, ff_mul_of_mem F N h2]

private theorem testFn_decomp (N : Ideal (𝓞 F)) (x : AdelicGL2 (𝓞 F) F)
    (hx : AdelicLevel.glFin (𝓞 F) F x ∈ Kf F N) :
    (adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x))⁻¹ * x ∈
      AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [AdelicLevel.mem_levelOne_iff, map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]
    exact hx
  · rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel]

private theorem glFin_mem_of_testFn_ne_zero (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F))
    (x : AdelicGL2 (𝓞 F) F) (hx : testFn F ρ hρ N x ≠ 0) : AdelicLevel.glFin (𝓞 F) F x ∈ Kf F N := by
  by_contra h
  exact hx (by simp only [testFn, ff, Set.indicator_of_notMem h, mul_zero])

private theorem testFn_support (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) (x : AdelicGL2 (𝓞 F) F)
    (hx : testFn F ρ hρ N x ≠ 0) :
    ∃ a k : AdelicGL2 (𝓞 F) F, AdelicLevel.glFin (𝓞 F) F a = 1 ∧
      k ∈ AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k :=
  ⟨adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x),
    (adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x))⁻¹ * x, glFin_adelicArchGLIncl F _,
    testFn_decomp F N x (glFin_mem_of_testFn_ne_zero F ρ hρ N x hx), (mul_inv_cancel_left _ _).symm⟩

private theorem testFn_eq_ofReal (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ ε F / 2) (N : Ideal (𝓞 F))
    (g : AdelicGL2 (𝓞 F) F) : testFn F ρ hρ N g = ((testFnR F ρ hρ N g : ℝ) : ℂ) := by
  simp only [testFn, testFnR, fa_eq F ρ hρ hρε, ff, Complex.ofReal_mul]
  congr 1
  by_cases h : AdelicLevel.glFin (𝓞 F) F g ∈ Kf F N
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.ofReal_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, Complex.ofReal_zero]

private theorem testFnR_nonneg (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) :
    0 ≤ testFnR F ρ hρ N g :=
  mul_nonneg (bumpAt F ρ hρ).nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

private theorem testFnR_one (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) : testFnR F ρ hρ N 1 = 1 := by
  have h1 : (bumpAt F ρ hρ).toFun (archEntries F 1) = 1 :=
    (bumpAt F ρ hρ).one_of_mem_closedBall (mem_closedBall_self (bumpAt F ρ hρ).rIn_pos.le)
  have h2 : (Kf F N).indicator (fun _ => (1 : ℝ)) 1 = 1 :=
    Set.indicator_of_mem
      (show (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) ∈ Kf F N from
        (AdelicLevel.finiteLevelOne (𝓞 F) F N).one_mem) _
  simp only [testFnR, map_one, h1, h2, mul_one]

private theorem of_testFnR_ne_zero (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) (x : AdelicGL2 (𝓞 F) F)
    (hx : testFnR F ρ hρ N x ≠ 0) :
    dist (archEntries F (AdelicLevel.glArch (𝓞 F) F x)) (cE F) < ρ ∧
      AdelicLevel.glFin (𝓞 F) F x ∈ Kf F N := by
  constructor
  · by_contra h
    rw [not_lt] at h
    have h0 : (bumpAt F ρ hρ).toFun (archEntries F (AdelicLevel.glArch (𝓞 F) F x)) = 0 :=
      (bumpAt F ρ hρ).zero_of_le_dist h
    exact hx (by simp only [testFnR, h0, zero_mul])
  · by_contra h
    exact hx (by simp only [testFnR, Set.indicator_of_notMem h, mul_zero])

private theorem rightConv_ne_zero_of_bound (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0) (f : AdelicGL2 (𝓞 F) F → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) (fR : AdelicGL2 (𝓞 F) F → ℝ) (hfR : ∀ x, f x = ((fR x : ℝ) : ℂ))
    (hR0 : ∀ x, 0 ≤ fR x) (hR1 : fR 1 ≠ 0)
    (hbound : ∀ x, fR x ≠ 0 → ‖φ (g₀ * x) - φ g₀‖ ≤ ‖φ g₀‖ / 2) :
    rightConv F φ f g₀ ≠ 0 := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hRre : fR = fun x => (f x).re := by
    funext x
    rw [hfR x, Complex.ofReal_re]
  have hRc : Continuous fR := by
    rw [hRre]
    exact Complex.continuous_re.comp hfc
  have hRs : HasCompactSupport fR := by
    rw [hRre]
    exact hfs.comp_left Complex.zero_re
  have hRi : Integrable fR (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    hRc.integrable_of_hasCompactSupport hRs
  have hIpos : 0 < ∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    (integral_pos_iff_support_of_nonneg (fun x => hR0 x) hRi).2
      (hRc.isOpen_support.measure_pos _ ⟨1, hR1⟩)
  have hmul : Continuous fun x : AdelicGL2 (𝓞 F) F => g₀ * x := continuous_const.mul continuous_id
  have hi₁ : Integrable (fun x => φ (g₀ * x) * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    ((hφ.comp hmul).mul hfc).integrable_of_hasCompactSupport hfs.mul_left
  have hi₂ : Integrable (fun x => φ g₀ * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    (hfc.integrable_of_hasCompactSupport hfs).const_mul _
  have h3 : ∫ x, f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
      = ((∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) : ℂ) := by
    simp only [hfR]
    exact integral_complex_ofReal
  intro h0
  have h2 : ∫ x, φ (g₀ * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) = 0 := h0
  have hint : ∫ x, (φ (g₀ * x) - φ g₀) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
      = -(φ g₀ * ((∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) : ℂ)) := by
    have h1 : (fun x => (φ (g₀ * x) - φ g₀) * f x) = fun x => φ (g₀ * x) * f x - φ g₀ * f x := by
      funext x
      ring
    rw [h1, integral_sub hi₁ hi₂, h2, integral_const_mul, h3, zero_sub]
  have hle : ‖∫ x, (φ (g₀ * x) - φ g₀) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)‖
      ≤ ∫ x, ‖φ g₀‖ / 2 * fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    refine norm_integral_le_of_norm_le (hRi.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, hfR x, Complex.norm_real, Real.norm_of_nonneg (hR0 x)]
    by_cases hx : fR x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_right (hbound x hx) (hR0 x)
  rw [hint, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hIpos.le,
    integral_const_mul] at hle
  have hc : 0 < ‖φ g₀‖ := norm_pos_iff.2 hg₀
  nlinarith [mul_pos hc hIpos]

end TestFnNearIdentity
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

end
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

noncomputable section

namespace TestFnNearIdentity

variable (F : Type) [Field F] [NumberField F]

private theorem exists_radius_of_continuous_uniformOn (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε F / 2 ∧ ∀ g ∈ C, ∀ m : GL (Fin 2) (InfiniteAdeleRing F),
      dist (archEntries F m) (cE F) < ρ →
        ‖φ (g * adelicArchGLIncl F m) - φ g‖ ≤ η := by
  have hψ : Continuous fun p : AdelicGL2 (𝓞 F) F × GL (Fin 2) (InfiniteAdeleRing F) =>
      φ (p.1 * adelicArchGLIncl F p.2) - φ p.1 :=
    (hφ.comp (continuous_fst.mul ((continuous_adelicArchGLIncl F).comp continuous_snd))).sub
      (hφ.comp continuous_fst)
  set W : Set (AdelicGL2 (𝓞 F) F × GL (Fin 2) (InfiniteAdeleRing F)) :=
    (fun p => φ (p.1 * adelicArchGLIncl F p.2) - φ p.1) ⁻¹' Metric.ball 0 η with hW
  have hWo : IsOpen W := Metric.isOpen_ball.preimage hψ
  have hsub : C ×ˢ ({1} : Set (GL (Fin 2) (InfiniteAdeleRing F))) ⊆ W := by
    rintro ⟨g, m⟩ ⟨-, hm⟩
    rw [Set.mem_singleton_iff] at hm
    subst hm
    show φ (g * adelicArchGLIncl F 1) - φ g ∈ Metric.ball (0 : ℂ) η
    rw [map_one, mul_one, sub_self]
    exact Metric.mem_ball_self hη
  obtain ⟨u, v, -, hv, hCu, h1v, huv⟩ := generalized_tube_lemma hC isCompact_singleton hWo hsub
  have hT : {m : GL (Fin 2) (InfiniteAdeleRing F) | ∀ g ∈ C, ‖φ (g * adelicArchGLIncl F m) - φ g‖ ≤ η} ∈
      𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)) := by
    refine Filter.mem_of_superset (hv.mem_nhds (h1v (Set.mem_singleton 1))) fun m hm g hg => ?_
    have h : (g, m) ∈ W := huv (Set.mk_mem_prod (hCu hg) hm)
    exact le_of_lt (mem_ball_zero_iff.1 h)
  obtain ⟨ρ, hρ, hρε, h⟩ := exists_radius F hT
  exact ⟨ρ, hρ, hρε, fun g hg m hm => h m hm g hg⟩

private theorem norm_rightConv_sub_mul_le (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (g : AdelicGL2 (𝓞 F) F) (f : AdelicGL2 (𝓞 F) F → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) (fR : AdelicGL2 (𝓞 F) F → ℝ) (hfR : ∀ x, f x = ((fR x : ℝ) : ℂ))
    (hR0 : ∀ x, 0 ≤ fR x) (η : ℝ)
    (hbound : ∀ x, fR x ≠ 0 → ‖φ (g * x) - φ g‖ ≤ η) :
    ‖rightConv F φ f g -
        ((letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
          ∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) : ℂ) * φ g‖ ≤
      η * (letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
          ∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hRre : fR = fun x => (f x).re := by
    funext x
    rw [hfR x, Complex.ofReal_re]
  have hRc : Continuous fR := by
    rw [hRre]
    exact Complex.continuous_re.comp hfc
  have hRs : HasCompactSupport fR := by
    rw [hRre]
    exact hfs.comp_left Complex.zero_re
  have hRi : Integrable fR (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    hRc.integrable_of_hasCompactSupport hRs
  have hmul : Continuous fun x : AdelicGL2 (𝓞 F) F => g * x := continuous_const.mul continuous_id
  have hi₁ : Integrable (fun x => φ (g * x) * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    ((hφ.comp hmul).mul hfc).integrable_of_hasCompactSupport hfs.mul_left
  have hi₂ : Integrable (fun x => φ g * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    (hfc.integrable_of_hasCompactSupport hfs).const_mul _
  have h3 : ∫ x, f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
      = ((∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) : ℂ) := by
    simp only [hfR]
    exact integral_complex_ofReal
  have hint : rightConv F φ f g -
      ((∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) : ℂ) * φ g
        = ∫ x, (φ (g * x) - φ g) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    have h1 : (fun x => (φ (g * x) - φ g) * f x) = fun x => φ (g * x) * f x - φ g * f x := by
      funext x
      ring
    rw [h1, integral_sub hi₁ hi₂, integral_const_mul, h3, rightConv_apply, mul_comm]
  have hle : ‖∫ x, (φ (g * x) - φ g) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)‖
      ≤ ∫ x, η * fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    refine norm_integral_le_of_norm_le (hRi.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, hfR x, Complex.norm_real, Real.norm_of_nonneg (hR0 x)]
    by_cases hx : fR x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_right (hbound x hx) (hR0 x)
  rw [hint]
  rwa [integral_const_mul] at hle

private theorem integral_pos_of_nonneg_of_apply_one_ne_zero (f : AdelicGL2 (𝓞 F) F → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) (fR : AdelicGL2 (𝓞 F) F → ℝ) (hfR : ∀ x, f x = ((fR x : ℝ) : ℂ))
    (hR0 : ∀ x, 0 ≤ fR x) (hR1 : fR 1 ≠ 0) :
    0 < (letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
          ∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hRre : fR = fun x => (f x).re := by
    funext x
    rw [hfR x, Complex.ofReal_re]
  have hRc : Continuous fR := by
    rw [hRre]
    exact Complex.continuous_re.comp hfc
  have hRs : HasCompactSupport fR := by
    rw [hRre]
    exact hfs.comp_left Complex.zero_re
  have hRi : Integrable fR (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    hRc.integrable_of_hasCompactSupport hRs
  exact (integral_pos_iff_support_of_nonneg (fun x => hR0 x) hRi).2
    (hRc.isOpen_support.measure_pos _ ⟨1, hR1⟩)

end TestFnNearIdentity
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

end
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

open _root_.NumberField _root_.NumberField.InfinitePlace.NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm in
open TestFnNearIdentity in

theorem Ws23.SMinf.exists_testFn_rightConv_sub_smul_le_uniformOn
    (F : Type) [Field F] [NumberField F]
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hlev : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      φ (g * k) = φ g)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C)
    (η : ℝ) (hη : 0 < η) :
    ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (c : ℝ), 0 < c ∧
      IsFactorizableTestFn F f ∧ (Continuous f ∧ HasCompactSupport f) ∧
      (∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, ∀ x, f (k * x) = f x) ∧
      (∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
        glFin (𝓞 F) F a = 1 ∧ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k) ∧
      (letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
        ∫ x, f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) = (c : ℂ)) ∧
      ∀ g ∈ C, ‖rightConv F φ f g - (c : ℂ) * φ g‖ ≤ η * c := by
  obtain ⟨ρ, hρ, hρε, hV⟩ := exists_radius_of_continuous_uniformOn F φ hcont C hC η hη
  have htier := isFactorizableTestFn_testFn F ρ hρ hρε hN
  obtain ⟨hfc, hfs⟩ :=
    AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F _ htier
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  refine ⟨testFn F ρ hρ N, ∫ x, testFnR F ρ hρ N x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F),
    integral_pos_of_nonneg_of_apply_one_ne_zero F _ hfc hfs (testFnR F ρ hρ N) (testFn_eq_ofReal F ρ hρ hρε N)
      (testFnR_nonneg F ρ hρ N) (by rw [testFnR_one]; exact one_ne_zero),
    htier, ⟨hfc, hfs⟩, fun _ hk x => testFn_mul_of_mem F ρ hρ N hk x,
    fun x hx => testFn_support F ρ hρ N x hx, ?_, fun g hg => ?_⟩
  · simp only [testFn_eq_ofReal F ρ hρ hρε N]
    exact integral_complex_ofReal
  · refine norm_rightConv_sub_mul_le F φ hcont g _ hfc hfs (testFnR F ρ hρ N)
      (testFn_eq_ofReal F ρ hρ hρε N) (testFnR_nonneg F ρ hρ N) η fun x hx => ?_
    obtain ⟨hdist, hfin⟩ := of_testFnR_ne_zero F ρ hρ N x hx
    have hx' : g * x = (g * adelicArchGLIncl F (glArch (𝓞 F) F x)) *
        ((adelicArchGLIncl F (glArch (𝓞 F) F x))⁻¹ * x) := by
      rw [mul_assoc, mul_inv_cancel_left]
    rw [hx', hlev _ _ (testFn_decomp F N x hfin)]
    exact hV g hg _ hdist

section SMinf_typed
p2m_open "IsDedekindDomain NumberField NumberField.InfinitePlace.NumberField MeasureTheory NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"

open Ws23.SMinf.Rot

theorem Ws23.SMinf.typed
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      Θ.toRawCentral)
    (hR : Continuous R.toFun)
    (w : InfinitePlace F) (hw : w.IsReal) (n : ℤ)
    (hn : HasArchCharacterAt₀ F w
      ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) R.toFun) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ),
      R.exceptionalSet ⊆ S ∧ IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
      rightConv F R.toFun f ≠ 0 ∧
      rightConv F R.toFun f ∈ isotypicCuspSubmodule F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
        R.centralChar Θ.level S Θ ∧
      rightConv F R.toFun f ∈ archCutSubmodule F tys ∧
      HasArchCharacterAt₀ F w
        ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) (rightConv F R.toFun f) ∧
      IsArchSmoothAt hw (rightConv F R.toFun f) ∧
      (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) (rightConv F R.toFun f)) ∧
        ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
          NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
            ‖l.foldr (archDerivAt hw) (rightConv F R.toFun f) g‖ ≤ B) := by
  set φ := R.toFun with hφdef
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  have hφpos : 0 < ‖φ g₀‖ := norm_pos_iff.2 hg₀

  set C : Set (AdelicGL2 (𝓞 F) F) := (fun θ : ℝ => g₀ * archRot w hw θ) '' Set.Icc 0 (2 * Real.pi) with hCdef
  have hC : IsCompact C := isCompact_Icc.image (continuous_const.mul (continuous_archRot w hw))
  have hCmem : ∀ θ : ℝ, g₀ * archRot w hw θ ∈ C := fun θ => by
    obtain ⟨θ', hθ', hθθ'⟩ := (archRot_periodic w hw).exists_mem_Ico₀ Real.two_pi_pos θ
    exact ⟨θ', Set.Ico_subset_Icc_self hθ', by simp only [hθθ']⟩
  have hg₀C : g₀ ∈ C := by simpa only [archRot_zero, mul_one] using hCmem 0

  obtain ⟨f₀, c₀, hc₀, hf₀, ⟨hf₀c, hf₀s⟩, -, hsupp₀, -, hb₁⟩ :=
    Ws23.SMinf.exists_testFn_rightConv_sub_smul_le_uniformOn F Θ.level Θ.level_ne_bot φ hR R.level_invariant C hC
      (‖φ g₀‖ / 4) (by positivity)
  have hg₀' : rightConv F φ f₀ g₀ ≠ 0 := by
    intro h0
    have h := hb₁ g₀ hg₀C
    rw [h0, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc₀.le] at h
    nlinarith [mul_pos hc₀ hφpos]
  obtain ⟨fa₀, ff, hfa₀, hff, hf₀eq⟩ := hf₀
  have hf₀fun : (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = f₀ := funext fun g => (hf₀eq g).symm
  have hne₀ : ∃ y₀, f₀ y₀ ≠ 0 := G1PrimeRat.ConvHalf.exists_ne_zero_of_rightConv_ne_zero F φ f₀ ⟨g₀, hg₀'⟩

  obtain ⟨tys, fa, hfa, hbi, -, hcut, hb₂, hfa', tys', hbi', hcut'⟩ :=
    Ws23.SMinf.exists_archFiniteVector_uniformOn_rotAvgArch F hw n φ hR fa₀ hfa₀ ff hff g₀
      (by rw [hf₀fun]; exact hg₀') C hC (c₀ * ‖φ g₀‖ / 4) (by positivity)
  set f : AdelicGL2 (𝓞 F) F → ℂ := fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g) with hfdef
  have hfact : IsFactorizableTestFn F f := ArchFiniteVector.ConvHalf.isFactorizableTestFn_mk F fa hfa ff hff
  obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hfact
  have hsuppf := G1PrimeRat.ConvHalf.support_shape_of_finFactor F Θ.level f₀ fa₀ ff hf₀eq hne₀ hsupp₀ f fa
    (fun _ => rfl)

  set f' : AdelicGL2 (𝓞 F) F → ℂ := fun g => rotAvgArch w hw n fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)
    with hf'def
  have hf'eq : f' = rotAvgL w hw n f := (rotAvgL_tensor n fa ff).symm
  have hfact' : IsFactorizableTestFn F f' := ArchFiniteVector.ConvHalf.isFactorizableTestFn_mk F _ hfa' ff hff
  have hconv : rightConv F φ f' = Pn w hw n (rightConv F φ f) := by
    rw [hf'eq]
    exact (Pn_rightConv n hR hfc hfs).symm
  have hsupp' : ∀ x, f' x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ levelOne (𝓞 F) F Θ.level ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k := by
    rw [hf'eq]
    exact rotAvgL_support n hsuppf

  have hcc : Continuous (rightConv F φ f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hR f hfact).1
  set E : AdelicGL2 (𝓞 F) F → ℂ := fun g => rightConv F φ f g - (c₀ : ℂ) * φ g with hEdef
  have hEc : Continuous E := hcc.sub (continuous_const.mul hR)
  have hsum : rightConv F φ f = E + (c₀ : ℂ) • φ := by
    funext g
    simp only [hEdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_add_cancel]
  have hEb : ∀ θ : ℝ, ‖E (g₀ * archRot w hw θ)‖ ≤ c₀ * ‖φ g₀‖ / 4 + ‖φ g₀‖ / 4 * c₀ := fun θ => by
    have h1 := hb₂ _ (hCmem θ)
    have h2 := hb₁ _ (hCmem θ)
    rw [hf₀fun] at h1
    calc ‖E (g₀ * archRot w hw θ)‖
        = ‖(rightConv F φ f (g₀ * archRot w hw θ) - rightConv F φ f₀ (g₀ * archRot w hw θ)) +
            (rightConv F φ f₀ (g₀ * archRot w hw θ) - (c₀ : ℂ) * φ (g₀ * archRot w hw θ))‖ := by
          simp only [hEdef, sub_add_sub_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 h2)
  have hPnE : ‖Pn w hw n E g₀‖ ≤ (c₀ * ‖φ g₀‖ / 4 + ‖φ g₀‖ / 4 * c₀) * |2 * Real.pi - 0| := norm_Pn_le n E hEb
  have hPn : Pn w hw n (rightConv F φ f) g₀ = Pn w hw n E g₀ + (c₀ : ℂ) * ((2 * Real.pi : ℂ) * φ g₀) := by
    have hsc : Continuous ((c₀ : ℂ) • φ) := hR.const_smul (c₀ : ℂ)
    rw [hsum, Pn_add n hEc hsc, Pn_smul, Pn_eq_smul_of_hasArchCharacterAt₀ n hn]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hne' : rightConv F φ f' ≠ 0 := by
    intro h0
    have h := congrFun h0 g₀
    rw [hconv, Pi.zero_apply, hPn] at h
    have h' : Pn w hw n E g₀ = -((c₀ : ℂ) * ((2 * Real.pi : ℂ) * φ g₀)) := eq_neg_of_add_eq_zero_left h
    rw [h', norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc₀.le,
      abs_of_nonneg (by linarith [Real.two_pi_pos] : (0:ℝ) ≤ 2 * Real.pi - 0)] at hPnE
    have h2π : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg Real.two_pi_pos.le]
    rw [h2π] at hPnE
    nlinarith [mul_pos (mul_pos hc₀ hφpos) Real.two_pi_pos, Real.pi_pos]

  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have hiso := G1PrimeRat.ConvHalf.isIsotypicCuspFormAt_rightConv_of_memLp F c u d₁ d₂ T Θ R hR f' hfact' hsupp'
    (SmwShell.memLp_rightConv_of_lt F c u d₁ d₂ T hd hc hd₁ hcov R.centralChar R.toFun R.smoothCusp hR f' hfact')
  refine ⟨R.exceptionalSet, tys', f', Finset.Subset.refl _, hfact', IsArchBiFinite.of_factorization F (fun _ => rfl) hbi',
    hne', hiso.mem_isotypicCuspSubmodule, hcut', ?_,
    ((AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw .H).1 R.toFun f' hR hfact').1,
    Ws23.SMinf.reg F c u d₁ d₂ T hc hd₁ hd hcov R.centralChar R.toFun R.smoothCusp hR f' hfact' hw⟩
  rw [show rightConv F R.toFun f' = Pn w hw n (rightConv F φ f) from hconv]
  exact hasArchCharacterAt₀_Pn n _

end SMinf_typed
p2m_reactivate "P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal.ArchFiniteVector.Poly"

p2m_open "IsDedekindDomain NumberField NumberField.InfinitePlace.NumberField"
p2m_open "NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion"
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      Θ.toRawCentral)
    (hR : Continuous R.toFun)
    (w : InfinitePlace F) (hw : w.IsReal) (n : ℤ)
    (hn : HasArchCharacterAt₀ F w
      ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) R.toFun) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ),
      R.exceptionalSet ⊆ S ∧ IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
      rightConv F R.toFun f ≠ 0 ∧
      rightConv F R.toFun f ∈ isotypicCuspSubmodule F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
        R.centralChar Θ.level S Θ ∧
      rightConv F R.toFun f ∈ archCutSubmodule F tys ∧
      HasArchCharacterAt₀ F w
        ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) (rightConv F R.toFun f) ∧
      IsArchSmoothAt hw (rightConv F R.toFun f) ∧
      (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) (rightConv F R.toFun f)) ∧
        ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
          NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
            ‖l.foldr (archDerivAt hw) (rightConv F R.toFun f) g‖ ≤ B) :=
  Ws23.SMinf.typed F c u d₁ d₂ T hc hd₁ hd hcov Θ R hR w hw n hn

end S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal
end P2MW
export P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal (solution)
