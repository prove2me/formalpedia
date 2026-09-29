-- Prove2me | solution 1 for AutomorphicForm.memLp_two_rightConv_restrict_of_isCuspAutomorphicFnAt_of_coversModCentre_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/fcc2783d-9ae4-51a2-8d56-2d4f2955cda1

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_SiegelVolume
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_NumberField_AdelicCentre
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_memLp_two_rightConv_restrict_of_isCuspAutomorphicFnAt_of_coversModCentre_of_pos
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.AdelicVolume NumberField.AdelicCentre NumberField.SiegelVolume

namespace Ws23
namespace L2Window

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.glBorel

scoped instance : BorelSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F

scoped instance : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

noncomputable def halfAt (w : InfinitePlace F) : (w.Completion)ˣ :=
  Units.mk0 ((2 : w.Completion)⁻¹) (inv_ne_zero (fun h => by
    have := norm_two_completion (F := F) w
    rw [h, norm_zero] at this
    norm_num at this))

noncomputable def ζDy (n : InfinitePlace F → ℕ) : (AdeleRing (𝓞 F) F)ˣ :=
  ∏ w : InfinitePlace F, (archCentralUnit F w (halfAt F w)) ^ (n w)

noncomputable def zDy (n : InfinitePlace F → ℕ) : AdelicGL2 (𝓞 F) F :=
  centralScalar (𝓞 F) F (ζDy F n)

theorem snd_prod_adele {ι : Type*} (s : Finset ι) (f : ι → AdeleRing (𝓞 F) F) :
    (∏ i ∈ s, f i).2 = ∏ i ∈ s, (f i).2 := by
  classical
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih => rw [Finset.prod_cons, Finset.prod_cons, ← ih]; rfl

theorem fst_prod_adele_apply {ι : Type*} (s : Finset ι) (f : ι → AdeleRing (𝓞 F) F) (w : InfinitePlace F) :
    (∏ i ∈ s, f i).1 w = ∏ i ∈ s, (f i).1 w := by
  classical
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih => rw [Finset.prod_cons, Finset.prod_cons, ← ih]; rfl

theorem snd_pow_adele (x : AdeleRing (𝓞 F) F) (k : ℕ) : (x ^ k).2 = x.2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem fst_pow_adele_apply (x : AdeleRing (𝓞 F) F) (k : ℕ) (w : InfinitePlace F) :
    (x ^ k).1 w = (x.1 w) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem ζDy_snd (n : InfinitePlace F → ℕ) : ((ζDy F n : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
  unfold ζDy
  rw [Units.coe_prod, snd_prod_adele]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [Units.val_pow_eq_pow_val, snd_pow_adele, archCentralUnit_snd, one_pow]

theorem ζDy_fst (n : InfinitePlace F → ℕ) (w : InfinitePlace F) :
    ((ζDy F n : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = ((2 : w.Completion)⁻¹) ^ (n w) := by
  classical
  unfold ζDy
  rw [Units.coe_prod, fst_prod_adele_apply, Finset.prod_eq_single w]
  · rw [Units.val_pow_eq_pow_val, fst_pow_adele_apply, archCentralUnit_fst_self]
    rfl
  · intro w' _ hw'
    rw [Units.val_pow_eq_pow_val, fst_pow_adele_apply, archCentralUnit_fst_of_ne w' _ (Ne.symm hw'), one_pow]
  · intro h; exact absurd (Finset.mem_univ w) h

theorem archComponent_centralScalar_apply (ζ : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) (i j : Fin 2) :
    ((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F ζ)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j
      = if i = j then ((ζ : AdeleRing (𝓞 F) F).1 w) else 0 := by
  rw [archComponent_apply, glArch_apply]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, if_pos rfl]
  · rw [centralScalar_apply_ne _ h, if_neg h]
    rfl

theorem archDetNorm_centralScalar_mul' (ζ : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm w (centralScalar (𝓞 F) F ζ * g)
      = (‖((ζ : AdeleRing (𝓞 F) F).1 w)‖ * ‖((ζ : AdeleRing (𝓞 F) F).1 w)‖) * archDetNorm w g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1
  rw [Matrix.det_fin_two, archComponent_centralScalar_apply, archComponent_centralScalar_apply,
    archComponent_centralScalar_apply, archComponent_centralScalar_apply]
  simp [norm_mul]

theorem localHeight_centralScalar_mul (ζ : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F)
    (hζ : ((ζ : AdeleRing (𝓞 F) F).1 w) ≠ 0) (g : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F ζ * g))) =
      localHeight (archComponent F w (glArch (𝓞 F) F g)) := by
  rw [map_mul, map_mul]
  refine localHeight_scalar_entries_mul hζ ?_ ?_ ?_ ?_ _
  · rw [archComponent_centralScalar_apply, if_pos rfl]
  · rw [archComponent_centralScalar_apply, if_neg (by decide)]
  · rw [archComponent_centralScalar_apply, if_neg (by decide)]
  · rw [archComponent_centralScalar_apply, if_pos rfl]

theorem xWindowSq_centralScalar_mul (ζ : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F)
    (hζ : ((ζ : AdeleRing (𝓞 F) F).1 w) ≠ 0) (g : AdelicGL2 (𝓞 F) F) :
    xWindowSq (archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F ζ * g))) =
      xWindowSq (archComponent F w (glArch (𝓞 F) F g)) := by
  rw [map_mul, map_mul]
  refine xWindowSq_scalar_entries_mul hζ ?_ ?_ ?_ ?_ _
  · rw [archComponent_centralScalar_apply, if_pos rfl]
  · rw [archComponent_centralScalar_apply, if_neg (by decide)]
  · rw [archComponent_centralScalar_apply, if_neg (by decide)]
  · rw [archComponent_centralScalar_apply, if_pos rfl]

theorem glFin_centralScalar_mul (ζ : (AdeleRing (𝓞 F) F)ˣ) (hζ : ((ζ : AdeleRing (𝓞 F) F).2) = 1)
    (g : AdelicGL2 (𝓞 F) F) :
    glFin (𝓞 F) F (centralScalar (𝓞 F) F ζ * g) = glFin (𝓞 F) F g := by
  rw [map_mul, glFin_scalar_eq_one F hζ (centralScalar_apply_eq ζ 0) (centralScalar_apply_ne ζ (by decide))
    (centralScalar_apply_ne ζ (by decide)) (centralScalar_apply_eq ζ 1), one_mul]

theorem ζDy_fst_ne_zero (n : InfinitePlace F → ℕ) (w : InfinitePlace F) :
    ((ζDy F n : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  rw [ζDy_fst]
  refine pow_ne_zero _ (inv_ne_zero fun h => ?_)
  have := norm_two_completion (F := F) w
  rw [h, norm_zero] at this
  norm_num at this

theorem archDetNorm_zDy_mul (n : InfinitePlace F → ℕ) (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm w (zDy F n * g) = ((4 : ℝ)⁻¹) ^ (n w) * archDetNorm w g := by
  unfold zDy
  rw [archDetNorm_centralScalar_mul', ζDy_fst, norm_pow, norm_inv, norm_two_completion, ← mul_pow]
  norm_num

theorem localHeight_zDy_mul (n : InfinitePlace F → ℕ) (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F w (glArch (𝓞 F) F (zDy F n * g))) =
      localHeight (archComponent F w (glArch (𝓞 F) F g)) :=
  localHeight_centralScalar_mul F _ w (ζDy_fst_ne_zero F n w) g

theorem xWindowSq_zDy_mul (n : InfinitePlace F → ℕ) (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    xWindowSq (archComponent F w (glArch (𝓞 F) F (zDy F n * g))) =
      xWindowSq (archComponent F w (glArch (𝓞 F) F g)) :=
  xWindowSq_centralScalar_mul F _ w (ζDy_fst_ne_zero F n w) g

theorem glFin_zDy_mul (n : InfinitePlace F → ℕ) (g : AdelicGL2 (𝓞 F) F) :
    glFin (𝓞 F) F (zDy F n * g) = glFin (𝓞 F) F g :=
  glFin_centralScalar_mul F _ (ζDy_snd F n) g

theorem units_inv_val_fst_apply (ζ : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    (((ζ⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w) = (((ζ : AdeleRing (𝓞 F) F).1 w))⁻¹ := by
  have h : ((ζ : AdeleRing (𝓞 F) F).1 w) * (((ζ⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w) = 1 := by
    have := congrArg (fun x : AdeleRing (𝓞 F) F => x.1 w) ζ.mul_inv
    exact this
  exact eq_inv_of_mul_eq_one_right h

theorem units_inv_val_snd (ζ : (AdeleRing (𝓞 F) F)ˣ) (hζ : ((ζ : AdeleRing (𝓞 F) F).2) = 1) :
    (((ζ⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) = 1 := by
  have h : ((ζ : AdeleRing (𝓞 F) F).2) * (((ζ⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) = 1 := by
    have := congrArg (fun x : AdeleRing (𝓞 F) F => x.2) ζ.mul_inv
    exact this
  rwa [hζ, one_mul] at h

theorem zDy_inv (n : InfinitePlace F → ℕ) : (zDy F n)⁻¹ = centralScalar (𝓞 F) F (ζDy F n)⁻¹ := by
  unfold zDy; rw [map_inv]

theorem ζDy_inv_fst (n : InfinitePlace F → ℕ) (w : InfinitePlace F) :
    (((ζDy F n)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = (2 : w.Completion) ^ (n w) := by
  rw [units_inv_val_fst_apply, ζDy_fst, inv_pow, inv_inv]

theorem archDetNorm_zDy_inv_mul (n : InfinitePlace F → ℕ) (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm w ((zDy F n)⁻¹ * g) = (4 : ℝ) ^ (n w) * archDetNorm w g := by
  rw [zDy_inv, archDetNorm_centralScalar_mul', ζDy_inv_fst, norm_pow, norm_two_completion, ← mul_pow]
  norm_num

theorem ζDy_inv_fst_ne_zero (n : InfinitePlace F → ℕ) (w : InfinitePlace F) :
    (((ζDy F n)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  rw [ζDy_inv_fst]
  refine pow_ne_zero _ (fun h => ?_)
  have := norm_two_completion (F := F) w
  rw [h, norm_zero] at this
  norm_num at this

theorem localHeight_zDy_inv_mul (n : InfinitePlace F → ℕ) (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F w (glArch (𝓞 F) F ((zDy F n)⁻¹ * g))) =
      localHeight (archComponent F w (glArch (𝓞 F) F g)) := by
  rw [zDy_inv]; exact localHeight_centralScalar_mul F _ w (ζDy_inv_fst_ne_zero F n w) g

theorem xWindowSq_zDy_inv_mul (n : InfinitePlace F → ℕ) (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    xWindowSq (archComponent F w (glArch (𝓞 F) F ((zDy F n)⁻¹ * g))) =
      xWindowSq (archComponent F w (glArch (𝓞 F) F g)) := by
  rw [zDy_inv]; exact xWindowSq_centralScalar_mul F _ w (ζDy_inv_fst_ne_zero F n w) g

theorem glFin_zDy_inv_mul (n : InfinitePlace F → ℕ) (g : AdelicGL2 (𝓞 F) F) :
    glFin (𝓞 F) F ((zDy F n)⁻¹ * g) = glFin (𝓞 F) F g := by
  rw [zDy_inv]; exact glFin_centralScalar_mul F _ (units_inv_val_snd F _ (ζDy_snd F n)) g

theorem archDetNorm_mul (w : InfinitePlace F) (g h : AdelicGL2 (𝓞 F) F) :
    archDetNorm w (g * h) = archDetNorm w g * archDetNorm w h := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

theorem exists_dyadic_exponent {a d₂ : ℝ} (ha : 0 < a) (had : a ≤ d₂) :
    ∃ k : ℕ, d₂ / 4 < (4 : ℝ) ^ k * a ∧ (4 : ℝ) ^ k * a ≤ d₂ := by
  classical
  have hex : ∃ k : ℕ, d₂ / 4 < (4 : ℝ) ^ k * a := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (d₂ / 4 / a) (by norm_num : (1 : ℝ) < 4)
    exact ⟨k, by rwa [div_lt_iff₀ ha] at hk⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h0 : Nat.find hex with _ | m
  · simpa using had
  · have hm : ¬ (d₂ / 4 < (4 : ℝ) ^ m * a) := Nat.find_min hex (by rw [h0]; exact Nat.lt_succ_self m)
    push Not at hm
    have : (4 : ℝ) ^ (m + 1) * a = 4 * ((4 : ℝ) ^ m * a) := by ring
    rw [this]
    linarith

theorem zDy_mul_mem_centreCutSiegelSet_iff (n : InfinitePlace F → ℕ) (c u d₁ d₂ : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    zDy F n * g ∈ centreCutSiegelSet F c u d₁ d₂ ↔
      (glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F ∧
        (∀ w : InfinitePlace F, c ≤ localHeight (archComponent F w (glArch (𝓞 F) F g))) ∧
        (∀ w : InfinitePlace F, xWindowSq (archComponent F w (glArch (𝓞 F) F g)) ≤ u ^ 2) ∧
        (∀ w : InfinitePlace F, ((4 : ℝ)⁻¹) ^ (n w) * archDetNorm w g ∈ Set.Icc d₁ d₂)) := by
  rw [mem_centreCutSiegelSet_iff, glFin_zDy_mul]
  simp only [localHeight_zDy_mul, xWindowSq_zDy_mul, archDetNorm_zDy_mul]

def baseShell (d₂ : ℝ) (A : Set (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F) :=
  A ∩ {g | ∀ w : InfinitePlace F, d₂ / 4 < archDetNorm w g ∧ archDetNorm w g ≤ d₂}

theorem mem_iUnion_shell_iff {c u d₁ d₂ : ℝ} (hd₁ : d₁ ≤ 0) (hd₂ : 0 < d₂) (x g : AdelicGL2 (𝓞 F) F) :
    g ∈ (· * x) '' centreCutSiegelSet F c u d₁ d₂ ↔
      ∃ n : InfinitePlace F → ℕ, (zDy F n)⁻¹ * g ∈
        (· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂) := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' := mem_centreCutSiegelSet_iff.mp hs
    choose n hn using fun w : InfinitePlace F =>
      exists_dyadic_exponent (archDetNorm_pos w s) (hs'.2.2.2 w).2
    refine ⟨n, (zDy F n)⁻¹ * s, ⟨?_, ?_⟩, ?_⟩
    rotate_left 2
    · show (zDy F n)⁻¹ * s * x = (zDy F n)⁻¹ * (s * x)
      rw [mul_assoc]
    · rw [mem_centreCutSiegelSet_iff, glFin_zDy_inv_mul]
      simp only [localHeight_zDy_inv_mul, xWindowSq_zDy_inv_mul, archDetNorm_zDy_inv_mul]
      refine ⟨hs'.1, hs'.2.1, hs'.2.2.1, fun w => ⟨?_, (hn w).2⟩⟩
      exact hd₁.trans (mul_pos (pow_pos (by norm_num) _) (archDetNorm_pos w s)).le
    · intro w
      show d₂ / 4 < archDetNorm w ((zDy F n)⁻¹ * s) ∧ archDetNorm w ((zDy F n)⁻¹ * s) ≤ d₂
      rw [archDetNorm_zDy_inv_mul]
      exact hn w
  · rintro ⟨n, b, ⟨hbS, hbdet⟩, hb⟩
    have hbdet' : ∀ w : InfinitePlace F, d₂ / 4 < archDetNorm w b ∧ archDetNorm w b ≤ d₂ := hbdet
    have hbS' := mem_centreCutSiegelSet_iff.mp hbS
    refine ⟨zDy F n * b, ?_, ?_⟩
    · rw [zDy_mul_mem_centreCutSiegelSet_iff]
      refine ⟨hbS'.1, hbS'.2.1, hbS'.2.2.1, fun w => ⟨?_, ?_⟩⟩
      · exact hd₁.trans (mul_pos (pow_pos (by norm_num) _) (archDetNorm_pos w b)).le
      · exact (mul_le_of_le_one_left (archDetNorm_pos w b).le
          (pow_le_one₀ (by norm_num) (by norm_num))).trans (hbdet' w).2
    · have hb' : b * x = (zDy F n)⁻¹ * g := hb
      show zDy F n * b * x = g
      rw [mul_assoc, hb', mul_inv_cancel_left]

theorem shell_disjoint {c u d₁ d₂ : ℝ} (hd₂ : 0 < d₂) (x : AdelicGL2 (𝓞 F) F)
    {n m : InfinitePlace F → ℕ} (hnm : n ≠ m) :
    Disjoint ((zDy F n * ·) '' ((· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂)))
      ((zDy F m * ·) '' ((· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂))) := by
  rw [Set.disjoint_left]
  rintro a ⟨_, ⟨b, ⟨-, hbdet⟩, rfl⟩, rfl⟩ ⟨_, ⟨b', ⟨-, hb'det⟩, rfl⟩, hEq⟩
  have hbdet' : ∀ w : InfinitePlace F, d₂ / 4 < archDetNorm w b ∧ archDetNorm w b ≤ d₂ := hbdet
  have hb'det' : ∀ w : InfinitePlace F, d₂ / 4 < archDetNorm w b' ∧ archDetNorm w b' ≤ d₂ := hb'det
  obtain ⟨w, hw⟩ := Function.ne_iff.mp hnm

  have hE : ((4 : ℝ)⁻¹) ^ (m w) * (archDetNorm w b' * archDetNorm w x)
      = ((4 : ℝ)⁻¹) ^ (n w) * (archDetNorm w b * archDetNorm w x) := by
    have := congrArg (archDetNorm w) hEq
    rwa [archDetNorm_zDy_mul, archDetNorm_zDy_mul, archDetNorm_mul, archDetNorm_mul] at this
  have hX : 0 < archDetNorm w x := archDetNorm_pos w x
  have hE' : ((4 : ℝ)⁻¹) ^ (m w) * archDetNorm w b' = ((4 : ℝ)⁻¹) ^ (n w) * archDetNorm w b := by
    have h1 : (((4 : ℝ)⁻¹) ^ (m w) * archDetNorm w b') * archDetNorm w x
        = (((4 : ℝ)⁻¹) ^ (n w) * archDetNorm w b) * archDetNorm w x := by
      rw [mul_assoc, mul_assoc]; exact hE
    exact mul_right_cancel₀ hX.ne' h1

  have key : ∀ (p q : ℕ) (A B : ℝ), p < q → d₂ / 4 < A → B ≤ d₂ → 0 < B →
      ((4 : ℝ)⁻¹) ^ q * B = ((4 : ℝ)⁻¹) ^ p * A → False := by
    intro p q A B hpq hA hB hB0 h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hpq
    have h4 : (0 : ℝ) < ((4 : ℝ)⁻¹) ^ p := pow_pos (by norm_num) _
    have h' : A = ((4 : ℝ)⁻¹) ^ (k + 1) * B := by
      have : ((4 : ℝ)⁻¹) ^ p * A = ((4 : ℝ)⁻¹) ^ p * (((4 : ℝ)⁻¹) ^ (k + 1) * B) := by
        rw [← h, ← mul_assoc, ← pow_add, add_assoc]
      exact mul_left_cancel₀ h4.ne' this
    have hk1 : ((4 : ℝ)⁻¹) ^ (k + 1) ≤ (4 : ℝ)⁻¹ := by
      rw [pow_succ]
      exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
    have : A ≤ (4 : ℝ)⁻¹ * B := by rw [h']; exact mul_le_mul_of_nonneg_right hk1 hB0.le
    linarith
  rcases lt_or_gt_of_ne hw with hlt | hgt
  · exact key (n w) (m w) (archDetNorm w b) (archDetNorm w b') hlt (hbdet' w).1 (hb'det' w).2
      (archDetNorm_pos w b') hE'
  · exact key (m w) (n w) (archDetNorm w b') (archDetNorm w b) hgt (hb'det' w).1 (hbdet' w).2
      (archDetNorm_pos w b) hE'.symm

theorem baseShell_subset {c u d₁ d₂ : ℝ} (x : AdelicGL2 (𝓞 F) F) :
    (· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂) ⊆ (· * x) '' centreCutSiegelSet F c u (d₂ / 4) d₂ := by
  rintro _ ⟨b, ⟨hbS, hbdet⟩, rfl⟩
  have hbdet' : ∀ w : InfinitePlace F, d₂ / 4 < archDetNorm w b ∧ archDetNorm w b ≤ d₂ := hbdet
  refine ⟨b, ?_, rfl⟩
  rw [mem_centreCutSiegelSet_iff] at hbS ⊢
  exact ⟨hbS.1, hbS.2.1, hbS.2.2.1, fun w => ⟨(hbdet' w).1.le, (hbdet' w).2⟩⟩

theorem lintegral_shell_eq (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    (h : AdelicGL2 (𝓞 F) F → ℂ) (z : AdelicGL2 (𝓞 F) F) (cz : ℂ) (hz : ∀ g, h (z * g) = cz * h g)
    (A : Set (AdelicGL2 (𝓞 F) F)) (hA : MeasurableSet A) :
    ∫⁻ g in (z * ·) '' A, ‖h g‖ₑ ^ 2 ∂μ = ‖cz‖ₑ ^ 2 * ∫⁻ g in A, ‖h g‖ₑ ^ 2 ∂μ := by
  set e : AdelicGL2 (𝓞 F) F ≃ᵐ AdelicGL2 (𝓞 F) F := MeasurableEquiv.mulLeft z with he
  have hecoe : (e : AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F) = (z * ·) := rfl
  have hmap : Measure.map e μ = μ := by rw [hecoe]; exact map_mul_left_eq_self μ z
  have hpre : e ⁻¹' ((z * ·) '' A) = A := by
    rw [hecoe]; exact Set.preimage_image_eq _ (mul_right_injective z)
  calc ∫⁻ g in (z * ·) '' A, ‖h g‖ₑ ^ 2 ∂μ
      = ∫⁻ g in (z * ·) '' A, ‖h g‖ₑ ^ 2 ∂(Measure.map e μ) := by rw [hmap]
    _ = ∫⁻ g, ‖h g‖ₑ ^ 2 ∂(Measure.map e (μ.restrict (e ⁻¹' ((z * ·) '' A)))) := by
        rw [MeasurableEquiv.restrict_map]
    _ = ∫⁻ g in A, ‖h (z * g)‖ₑ ^ 2 ∂μ := by rw [lintegral_map_equiv, hpre]; rfl
    _ = ∫⁻ g in A, ‖cz‖ₑ ^ 2 * ‖h g‖ₑ ^ 2 ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [hz, enorm_mul, mul_pow]
    _ = ‖cz‖ₑ ^ 2 * ∫⁻ g in A, ‖h g‖ₑ ^ 2 ∂μ :=
        lintegral_const_mul' _ _ (by simp)

theorem measurableSet_baseShell_image {c u d₁ d₂ : ℝ} (x : AdelicGL2 (𝓞 F) F) :
    MeasurableSet ((· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂)) := by
  rw [Set.image_mul_right]
  refine (measurable_mul_const x⁻¹) ?_
  refine (measurableSet_centreCutSiegelSet c u d₁ d₂).inter ?_
  have : {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F, d₂ / 4 < archDetNorm w g ∧ archDetNorm w g ≤ d₂}
      = ⋂ w : InfinitePlace F, (archDetNorm w) ⁻¹' Set.Ioc (d₂ / 4) d₂ := by
    ext g; simp [Set.mem_Ioc]
  rw [this]
  exact MeasurableSet.iInter fun w => (continuous_archDetNorm w).measurable measurableSet_Ioc

theorem adelicGLHaar_image_mul_right_centreCutSiegelSet_lt_top {c u d₁ d₂ : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁)
    (x : AdelicGL2 (𝓞 F) F) :
    adelicGLHaar (Fin 2) (𝓞 F) F ((· * x) '' centreCutSiegelSet F c u d₁ d₂) < ⊤ := by
  have himage : (· * x) '' centreCutSiegelSet F c u d₁ d₂ = (· * x⁻¹) ⁻¹' centreCutSiegelSet F c u d₁ d₂ := by
    ext g
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rwa [mul_inv_cancel_right]
    · intro hg
      exact ⟨g * x⁻¹, hg, by rw [inv_mul_cancel_right]⟩
  rw [himage, ← Measure.map_apply (measurable_mul_const x⁻¹) (measurableSet_centreCutSiegelSet c u d₁ d₂)]
  exact measure_centreCutSiegelSet_lt_top _ hc u hd₁ d₂

theorem measurableSet_image_mul_right_centreCutSiegelSet (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) :
    MeasurableSet ((· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
  have himage : (· * x) '' centreCutSiegelSet F c u d₁ d₂ = (· * x⁻¹) ⁻¹' centreCutSiegelSet F c u d₁ d₂ := by
    ext g
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rwa [mul_inv_cancel_right]
    · intro hg
      exact ⟨g * x⁻¹, hg, by rw [inv_mul_cancel_right]⟩
  rw [himage]
  exact (measurable_mul_const x⁻¹) (measurableSet_centreCutSiegelSet c u d₁ d₂)

theorem memLp_two_restrict_of_bound_of_measure_lt_top (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : Continuous h)
    (A : Set (AdelicGL2 (𝓞 F) F)) (hAm : MeasurableSet A) (hA : adelicGLHaar (Fin 2) (𝓞 F) F A < ⊤) (C : ℝ)
    (hC : ∀ g ∈ A, ‖h g‖ ≤ C) : MemLp h 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict A) := by
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict A) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hA⟩
  refine MemLp.of_bound hh.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' hAm]
  exact Filter.Eventually.of_forall hC

theorem memLp_two_rightConv_window_of_pos_of_pos
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    MemLp (rightConv F φ f) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
  obtain ⟨C, hC⟩ :=
    AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
      F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf c u d₁ d₂ T hc hd₁
  have hcont' : Continuous (rightConv F φ f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hcont f hf).1
  refine memLp_two_restrict_of_bound_of_measure_lt_top F (rightConv F φ f) hcont' _ ?_ ?_ C hC
  · exact MeasurableSet.biUnion T.countable_toSet fun x _ =>
      measurableSet_image_mul_right_centreCutSiegelSet F c u d₁ d₂ x
  · refine (measure_biUnion_finset_le T _).trans_lt ?_
    exact ENNReal.sum_lt_top.mpr fun x _ => adelicGLHaar_image_mul_right_centreCutSiegelSet_lt_top F hc hd₁ x

section L2b
variable {F}

local notation "μH" => adelicGLHaar (Fin 2) (𝓞 F) F

open scoped NNReal ENNReal

theorem shell_subset {c u d₁ d₂ : ℝ} (hd₁ : d₁ ≤ 0) (x : AdelicGL2 (𝓞 F) F) (n : InfinitePlace F → ℕ) :
    (zDy F n * ·) '' ((· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂)) ⊆
      (· * x) '' centreCutSiegelSet F c u d₁ d₂ := by
  rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  refine ⟨zDy F n * b, ?_, mul_assoc _ _ _⟩
  obtain ⟨hbS, hbdet⟩ := hb
  obtain ⟨hfin, hfloor, hwin, -⟩ := mem_centreCutSiegelSet_iff.mp hbS
  refine (zDy_mul_mem_centreCutSiegelSet_iff F n c u d₁ d₂ b).mpr ⟨hfin, hfloor, hwin, fun w => ?_⟩
  have h4 : (0 : ℝ) < ((4 : ℝ)⁻¹) ^ n w := pow_pos (by norm_num) _
  have h4' : ((4 : ℝ)⁻¹) ^ n w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpos := archDetNorm_pos w b
  refine ⟨hd₁.trans (mul_pos h4 hpos).le, ?_⟩
  calc ((4 : ℝ)⁻¹) ^ n w * archDetNorm w b ≤ 1 * archDetNorm w b := by gcongr
    _ = archDetNorm w b := one_mul _
    _ ≤ d₂ := (hbdet w).2

theorem subset_iUnion_shell {c u d₁ d₂ : ℝ} (hd₁ : d₁ ≤ 0) (hd₂ : 0 < d₂) (x : AdelicGL2 (𝓞 F) F) :
    (· * x) '' centreCutSiegelSet F c u d₁ d₂ ⊆
      ⋃ n : InfinitePlace F → ℕ,
        (zDy F n * ·) '' ((· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂)) := by
  intro g hg
  obtain ⟨n, hn⟩ := (mem_iUnion_shell_iff F hd₁ hd₂ x g).mp hg
  exact Set.mem_iUnion.mpr ⟨n, (zDy F n)⁻¹ * g, hn, mul_inv_cancel_left _ _⟩

theorem measurableSet_shell {c u d₁ d₂ : ℝ} (x : AdelicGL2 (𝓞 F) F) (n : InfinitePlace F → ℕ) :
    MeasurableSet ((zDy F n * ·) '' ((· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂))) := by
  rw [Set.image_mul_left]
  exact (measurable_const_mul _) (measurableSet_baseShell_image F x)

theorem lintegral_translate_le_tsum {c u d₁ d₂ : ℝ} (hd₁ : d₁ ≤ 0) (hd₂ : 0 < d₂) (x : AdelicGL2 (𝓞 F) F)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (cz : (InfinitePlace F → ℕ) → ℂ)
    (hh : ∀ (n : InfinitePlace F → ℕ) (g : AdelicGL2 (𝓞 F) F), h (zDy F n * g) = cz n * h g) :
    ∫⁻ g in (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖h g‖ₑ ^ 2 ∂μH ≤
      ∑' n : InfinitePlace F → ℕ, ‖cz n‖ₑ ^ 2 *
        ∫⁻ g in (· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂), ‖h g‖ₑ ^ 2 ∂μH := by
  calc ∫⁻ g in (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖h g‖ₑ ^ 2 ∂μH
      ≤ ∫⁻ g in ⋃ n : InfinitePlace F → ℕ,
          (zDy F n * ·) '' ((· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂)), ‖h g‖ₑ ^ 2 ∂μH :=
        lintegral_mono_set (subset_iUnion_shell hd₁ hd₂ x)
    _ ≤ ∑' n : InfinitePlace F → ℕ,
          ∫⁻ g in (zDy F n * ·) '' ((· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂)), ‖h g‖ₑ ^ 2 ∂μH :=
        lintegral_iUnion_le _ _
    _ = _ := tsum_congr fun n =>
        lintegral_shell_eq F _ h (zDy F n) (cz n) (hh n) _ (measurableSet_baseShell_image F x)

theorem tsum_mul_lintegral_baseShell_le {c u d₁ d₂ : ℝ} (hd₁ : d₁ ≤ 0) (hd₂ : 0 < d₂)
    (x : AdelicGL2 (𝓞 F) F) (h : AdelicGL2 (𝓞 F) F → ℂ) (cz : (InfinitePlace F → ℕ) → ℂ)
    (hh : ∀ (n : InfinitePlace F → ℕ) (g : AdelicGL2 (𝓞 F) F), h (zDy F n * g) = cz n * h g) :
    ∑' n : InfinitePlace F → ℕ, ‖cz n‖ₑ ^ 2 *
        ∫⁻ g in (· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂), ‖h g‖ₑ ^ 2 ∂μH ≤
      ∫⁻ g in (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖h g‖ₑ ^ 2 ∂μH := by
  calc ∑' n : InfinitePlace F → ℕ, ‖cz n‖ₑ ^ 2 *
        ∫⁻ g in (· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂), ‖h g‖ₑ ^ 2 ∂μH
      = ∑' n : InfinitePlace F → ℕ,
          ∫⁻ g in (zDy F n * ·) '' ((· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂)), ‖h g‖ₑ ^ 2 ∂μH :=
        tsum_congr fun n =>
          (lintegral_shell_eq F _ h (zDy F n) (cz n) (hh n) _ (measurableSet_baseShell_image F x)).symm
    _ = ∫⁻ g in ⋃ n : InfinitePlace F → ℕ,
          (zDy F n * ·) '' ((· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂)), ‖h g‖ₑ ^ 2 ∂μH :=
        (lintegral_iUnion (measurableSet_shell x) (fun n m hnm => shell_disjoint F hd₂ x hnm) _).symm
    _ ≤ _ := lintegral_mono_set (Set.iUnion_subset fun n => shell_subset hd₁ x n)

variable (F) in
theorem countable_numberField : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

variable (F) in
theorem countable_gl2 : Countable (GL (Fin 2) F) := by
  haveI := countable_numberField F
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  exact Function.Injective.countable (f := fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) fun _ _ h => Units.ext h

open NumberField.TateGlobal in
theorem eq_zero_of_forall_lintegral_baseShell_eq_zero {c u d₁ d₂ : ℝ} (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd₁ : d₁ ≤ 0) (hd₂ : 0 < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (hcont : Continuous φ)
    (h0 : ∀ x ∈ T, ∫⁻ g in (· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ₑ ^ 2 ∂μH = 0) :
    φ = 0 := by
  have hd : d₁ < d₂ := hd₁.trans_lt hd₂
  have hcen : ∀ (ζ : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F ζ * g) = ((ξ ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * φ g :=
    fun ζ g => hφ.central_transform ⟨ζ, Subgroup.mem_top ζ⟩ g

  have hA : ∀ x ∈ T, μH ({g | φ g ≠ 0} ∩ (· * x) '' centreCutSiegelSet F c u d₁ d₂) = 0 := by
    intro x hx
    have hint : ∫⁻ g in (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖φ g‖ₑ ^ 2 ∂μH = 0 := by
      refine le_antisymm ?_ bot_le
      refine (lintegral_translate_le_tsum hd₁ hd₂ x φ
        (fun n => ((ξ ⟨ζDy F n, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) (fun n g => hcen (ζDy F n) g)).trans ?_
      rw [h0 x hx]
      simp
    have hmeas : Measurable fun g => ‖φ g‖ₑ ^ 2 := hcont.measurable.enorm.pow_const _
    rw [lintegral_eq_zero_iff hmeas, Filter.EventuallyEq,
      ae_restrict_iff' (measurableSet_image_mul_right_centreCutSiegelSet F c u d₁ d₂ x)] at hint
    have hae : ({g | φ g ≠ 0} ∩ (· * x) '' centreCutSiegelSet F c u d₁ d₂)ᶜ ∈ ae μH := by
      filter_upwards [hint] with g hg
      rintro ⟨hne, hmem⟩
      have h2 : ‖φ g‖ₑ ^ 2 = 0 := hg hmem
      exact hne (by simpa using h2)
    have := mem_ae_iff.mp hae
    rwa [compl_compl] at this

  obtain ⟨sec, -, hsec, -⟩ := exists_continuous_monoidHom_ideleNorm_apply_eq F
  set z₁ : (AdeleRing (𝓞 F) F)ˣ := sec (Units.mk0 (2 : ℝ≥0) two_ne_zero) with hz₁_def
  have hz₁ : ideleNorm F z₁ = 2 := by
    rw [hz₁_def, hsec, Units.val_mk0, NNReal.coe_ofNat]
  have hpow : ∀ j : ℤ, ideleNorm F (z₁ ^ j) = 2 ^ j := by
    intro j
    unfold ideleNorm at hz₁ ⊢
    rw [map_zpow, NNReal.coe_zpow, hz₁]
  have hdet : ∀ (ζ : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F ζ * g) =
        ζ * ζ * Matrix.GeneralLinearGroup.det g := by
    intro ζ g
    rw [map_mul]
    congr 1
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, centralScalar_apply_eq,
      centralScalar_apply_eq, centralScalar_apply_ne ζ (by decide : (0 : Fin 2) ≠ 1), zero_mul, sub_zero,
      Units.val_mul]
  have hnorm : ∀ (j : ℤ) (g : AdelicGL2 (𝓞 F) F),
      ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (z₁ ^ j) * g)) =
        (4 : ℝ) ^ j * ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
    intro j g
    rw [hdet, ideleNorm_mul, ideleNorm_mul, hpow, ← mul_zpow]
    norm_num
  have hj : ∀ g : AdelicGL2 (𝓞 F) F, ∃ j : ℤ,
      ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (z₁ ^ j) * g)) ∈ Set.Icc (1 : ℝ) 4 := by
    intro g
    have hNg := ideleNorm_pos (F := F) (Matrix.GeneralLinearGroup.det g)
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow (inv_pos.mpr hNg) (by norm_num : (1 : ℝ) < 4)
    refine ⟨n + 1, ?_⟩
    rw [hnorm]
    have h1 := mul_lt_mul_of_pos_right hn2 hNg
    have h2 := mul_le_mul_of_nonneg_right hn1 hNg.le
    rw [inv_mul_cancel₀ hNg.ne'] at h1 h2
    refine ⟨h1.le, ?_⟩
    rw [zpow_add_one₀ (four_ne_zero), mul_comm _ (4 : ℝ), mul_assoc]
    linarith
  obtain ⟨Nset, hN⟩ :=
    AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T hd hcov 1 4 one_pos

  have hcover : {g | φ g ≠ 0} ⊆ ⋃ j : ℤ, ⋃ γ : GL (Fin 2) F, ⋃ n ∈ Nset, ⋃ x ∈ T,
      ((centralScalar (𝓞 F) F (z₁ ^ j))⁻¹ * (globalPoints (𝓞 F) F γ)⁻¹ * centralScalar (𝓞 F) F n * ·) ''
        ({g | φ g ≠ 0} ∩ (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
    intro g hg
    obtain ⟨j, hjg⟩ := hj g
    obtain ⟨γ, n, hn, x, hx, s, hs, hsx⟩ := hN _ hjg
    dsimp only at hsx
    simp only [Set.mem_iUnion]
    refine ⟨j, γ, n, hn, x, hx, s * x, ⟨?_, s, hs, rfl⟩, ?_⟩
    · intro h0'
      apply hg
      have e1 : φ (globalPoints (𝓞 F) F γ * (centralScalar (𝓞 F) F (z₁ ^ j) * g)) =
          ((ξ ⟨z₁ ^ j, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * φ g := by
        rw [hφ.left_invariant, hcen]
      have e2 : φ (s * (centralScalar (𝓞 F) F n * x)) = ((ξ ⟨n, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * φ (s * x) := by
        rw [← mul_assoc, mul_centralScalar_comm n s, mul_assoc, hcen]
      rw [hsx, e1, h0', mul_zero] at e2
      exact (mul_eq_zero.mp e2).resolve_left (Units.ne_zero _)
    · have e3 : centralScalar (𝓞 F) F n * (s * x) =
          globalPoints (𝓞 F) F γ * (centralScalar (𝓞 F) F (z₁ ^ j) * g) := by
        rw [← hsx, ← mul_assoc, ← mul_centralScalar_comm n s, mul_assoc]
      show (centralScalar (𝓞 F) F (z₁ ^ j))⁻¹ * (globalPoints (𝓞 F) F γ)⁻¹ * centralScalar (𝓞 F) F n *
          (s * x) = g
      rw [mul_assoc _ (centralScalar (𝓞 F) F n), e3]
      group

  have hNull : μH {g | φ g ≠ 0} = 0 := by
    refine measure_mono_null hcover ?_
    haveI := countable_gl2 F
    refine measure_iUnion_null fun j => measure_iUnion_null fun γ => ?_
    refine (measure_biUnion_null_iff Nset.countable_toSet).mpr fun n _ => ?_
    refine (measure_biUnion_null_iff T.countable_toSet).mpr fun x hx => ?_
    rw [Set.image_mul_left, measure_preimage_mul]
    exact hA x hx
  have hNo : IsOpen {g | φ g ≠ 0} := isOpen_ne_fun hcont continuous_const
  have hNempty : {g | φ g ≠ 0} = ∅ := (hNo.measure_eq_zero_iff μH).mp hNull
  funext g
  by_contra hg
  exact (Set.eq_empty_iff_forall_notMem.mp hNempty g) hg

theorem memLp_two_rightConv_window_of_nonpos_of_pos
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : d₁ ≤ 0) (hd₂ : 0 < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    MemLp (rightConv F φ f) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
  have hd : d₁ < d₂ := hd₁.trans_lt hd₂
  obtain ⟨hLs, hL2⟩ := (lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ φ).mp hφ.1
  have hcen : ∀ (ζ : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F ζ * g) = ((ξ ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * φ g :=
    fun ζ g => hLs.central_transform ⟨ζ, Subgroup.mem_top ζ⟩ g
  have hcen' : ∀ (ζ : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      rightConv F φ f (centralScalar (𝓞 F) F ζ * g) =
        ((ξ ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * rightConv F φ f g := by
    intro ζ g
    rw [← rightConv_comp_mul_left]
    simp only [hcen, rightConv, mul_assoc]
    exact integral_const_mul _ _
  have hcontc : Continuous (rightConv F φ f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hcont f hf).1
  obtain ⟨C, hC⟩ :=
    AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
      F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf c u (d₂ / 4) d₂ T hc (by positivity)

  set cξ : (InfinitePlace F → ℕ) → ℂ := fun n => ((ξ ⟨ζDy F n, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) with hcξ

  have hA : ∀ x ∈ T, ∫⁻ g in (· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂), ‖rightConv F φ f g‖ₑ ^ 2 ∂μH < ⊤ := by
    intro x hx
    calc ∫⁻ g in (· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂), ‖rightConv F φ f g‖ₑ ^ 2 ∂μH
        ≤ ∫⁻ g in (· * x) '' centreCutSiegelSet F c u (d₂ / 4) d₂, ‖rightConv F φ f g‖ₑ ^ 2 ∂μH :=
          lintegral_mono_set (baseShell_subset F x)
      _ ≤ ∫⁻ g in (· * x) '' centreCutSiegelSet F c u (d₂ / 4) d₂, (ENNReal.ofReal C) ^ 2 ∂μH := by
          refine setLIntegral_mono' (measurableSet_image_mul_right_centreCutSiegelSet F c u _ _ x)
            fun g hg => ?_
          have hgC : ‖rightConv F φ f g‖ ≤ C := hC g (Set.mem_iUnion₂.mpr ⟨x, hx, hg⟩)
          rw [← ofReal_norm]
          exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal hgC) 2
      _ = (ENNReal.ofReal C) ^ 2 * μH ((· * x) '' centreCutSiegelSet F c u (d₂ / 4) d₂) :=
          setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          (adelicGLHaar_image_mul_right_centreCutSiegelSet_lt_top F hc (by positivity) x)

  have hφD : ∫⁻ g in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖φ g‖ₑ ^ 2 ∂μH < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hL2.eLpNorm_lt_top
    simp [ENNReal.toReal_ofNat] at this ⊢
    exact this

  have hSB : ∀ x ∈ T, (∑' n, ‖cξ n‖ₑ ^ 2) * ∫⁻ g in (· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ₑ ^ 2 ∂μH ≤
      ∫⁻ g in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖φ g‖ₑ ^ 2 ∂μH := by
    intro x hx
    calc (∑' n, ‖cξ n‖ₑ ^ 2) * ∫⁻ g in (· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ₑ ^ 2 ∂μH
        = ∑' n, ‖cξ n‖ₑ ^ 2 * ∫⁻ g in (· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ₑ ^ 2 ∂μH :=
          ENNReal.tsum_mul_right.symm
      _ ≤ ∫⁻ g in (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖φ g‖ₑ ^ 2 ∂μH :=
          tsum_mul_lintegral_baseShell_le hd₁ hd₂ x φ cξ (fun n g => hcen _ g)
      _ ≤ _ := lintegral_mono_set (Set.subset_iUnion₂ (s := fun x (_ : x ∈ T) => (· * x) '' centreCutSiegelSet F c u d₁ d₂) x hx)
  by_cases hB : ∃ x ∈ T, ∫⁻ g in (· * x) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ₑ ^ 2 ∂μH ≠ 0
  · obtain ⟨x₀, hx₀, hB₀⟩ := hB
    have hSfin : (∑' n, ‖cξ n‖ₑ ^ 2) < ⊤ := by
      by_contra htop
      rw [not_lt, top_le_iff] at htop
      have := hSB x₀ hx₀
      rw [htop, ENNReal.top_mul hB₀, top_le_iff] at this
      exact hφD.ne this
    have hsub : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ⊆ ⋃ x : T, (· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁ d₂ := by
      intro g hg
      simp only [Set.mem_iUnion] at hg ⊢
      obtain ⟨x, hx, h⟩ := hg
      exact ⟨⟨x, hx⟩, h⟩
    have hmain : ∫⁻ g in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖rightConv F φ f g‖ₑ ^ 2 ∂μH < ⊤ := by
      calc ∫⁻ g in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖rightConv F φ f g‖ₑ ^ 2 ∂μH
          ≤ ∫⁻ g in ⋃ x : T, (· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁ d₂, ‖rightConv F φ f g‖ₑ ^ 2 ∂μH :=
            lintegral_mono_set hsub
        _ ≤ ∑' x : T, ∫⁻ g in (· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁ d₂, ‖rightConv F φ f g‖ₑ ^ 2 ∂μH :=
            lintegral_iUnion_le _ _
        _ ≤ ∑' x : T, (∑' n, ‖cξ n‖ₑ ^ 2) *
              ∫⁻ g in (· * (x : AdelicGL2 (𝓞 F) F)) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂), ‖rightConv F φ f g‖ₑ ^ 2 ∂μH :=
            ENNReal.tsum_le_tsum fun x =>
              (lintegral_translate_le_tsum hd₁ hd₂ (x : AdelicGL2 (𝓞 F) F) (rightConv F φ f) cξ
                (fun n g => hcen' _ g)).trans_eq ENNReal.tsum_mul_right
        _ = ∑ x : T, (∑' n, ‖cξ n‖ₑ ^ 2) *
              ∫⁻ g in (· * (x : AdelicGL2 (𝓞 F) F)) '' baseShell F d₂ (centreCutSiegelSet F c u d₁ d₂), ‖rightConv F φ f g‖ₑ ^ 2 ∂μH :=
            tsum_fintype _
        _ < ⊤ := ENNReal.sum_lt_top.mpr fun x _ => ENNReal.mul_lt_top hSfin (hA x x.2)
    refine ⟨hcontc.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simpa [ENNReal.toReal_ofNat] using hmain
  · push Not at hB
    have hφ0 : φ = 0 := eq_zero_of_forall_lintegral_baseShell_eq_zero T hd₁ hd₂ hcov ξ φ hLs hcont hB
    have h0 : rightConv F φ f = fun _ => 0 := by
      rw [hφ0]
      exact rightConv_zero_left F f
    rw [h0]
    exact MemLp.zero'

theorem memLp_two_rightConv_window
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    MemLp (rightConv F φ f) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
  rcases lt_or_ge 0 d₁ with hd₁ | hd₁
  · exact memLp_two_rightConv_window_of_pos_of_pos F c u d₁ d₂ T hc hd₁ hd hcov ξ φ hφ hcont f hf
  rcases lt_or_ge 0 d₂ with hd₂ | hd₂
  · exact memLp_two_rightConv_window_of_nonpos_of_pos c u d₁ d₂ T hc hd₁ hd₂ hcov ξ φ hφ hcont f hf
  · have hempty : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun g hg => ?_
      simp only [Set.mem_iUnion, Set.mem_image] at hg
      obtain ⟨x, -, s, hs, -⟩ := hg
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
      have h1 := ((mem_centreCutSiegelSet_iff.mp hs).2.2.2 w).2
      linarith [archDetNorm_pos w s]
    rw [hempty, Measure.restrict_empty]
    exact ⟨aestronglyMeasurable_zero_measure _, by simp⟩

end L2b

end Ws23.L2Window
p2m_reactivate "P2MW.S_AutomorphicForm_memLp_two_rightConv_restrict_of_isCuspAutomorphicFnAt_of_coversModCentre_of_pos.Ws23 P2MW.S_AutomorphicForm_memLp_two_rightConv_restrict_of_isCuspAutomorphicFnAt_of_coversModCentre_of_pos.Ws23.L2Window"
p2m_reactivate "P2MW.S_AutomorphicForm_memLp_two_rightConv_restrict_of_isCuspAutomorphicFnAt_of_coversModCentre_of_pos.Ws23"

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    MemLp (rightConv F φ f) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :=
  Ws23.L2Window.memLp_two_rightConv_window c u d₁ d₂ T hc hd hcov ξ φ hφ hcont f hf

end S_AutomorphicForm_memLp_two_rightConv_restrict_of_isCuspAutomorphicFnAt_of_coversModCentre_of_pos
end P2MW
export P2MW.S_AutomorphicForm_memLp_two_rightConv_restrict_of_isCuspAutomorphicFnAt_of_coversModCentre_of_pos (solution)
