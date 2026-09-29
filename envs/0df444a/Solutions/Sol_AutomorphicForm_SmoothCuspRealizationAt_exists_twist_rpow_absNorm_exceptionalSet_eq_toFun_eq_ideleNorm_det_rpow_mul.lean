-- Prove2me | solution 1 for AutomorphicForm.SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6b9c0073-c83e-5720-914e-71a54cd87a7d

import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_FnTwist
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
open LanglandsTunnell LanglandsTunnell.Converse

noncomputable section

namespace TwistRpow

open MeasureTheory Matrix FLT.SmoothVectors AutomorphicForm.SmoothCusp HeckeIntegralSeam
open NumberField.AdelicHaar NumberField.AdelicVolume

variable (K : Type) [Field K] [NumberField K]

theorem ideleNorm_one' : ideleNorm K 1 = 1 := by
  have h := ideleNorm_mul (1 : (AdeleRing (𝓞 K) K)ˣ) 1
  rw [mul_one] at h
  exact (mul_eq_left₀ (ideleNorm_pos (1 : (AdeleRing (𝓞 K) K)ˣ)).ne').mp h.symm

theorem ofReal_ideleNorm_rpow_ne_zero (x : (AdeleRing (𝓞 K) K)ˣ) (s : ℝ) :
    (((ideleNorm K x) ^ s : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (ideleNorm_pos x) s).ne'

def nchar (s : ℝ) : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ where
  toFun x := Units.mk0 (((ideleNorm K x) ^ s : ℝ) : ℂ) (ofReal_ideleNorm_rpow_ne_zero K x s)
  map_one' := Units.ext (by
    rw [Units.val_mk0, ideleNorm_one', Real.one_rpow, Complex.ofReal_one, Units.val_one])
  map_mul' x y := Units.ext (by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, ideleNorm_mul,
      Real.mul_rpow (ideleNorm_pos x).le (ideleNorm_pos y).le, Complex.ofReal_mul])

variable {K}

theorem coe_nchar_apply (s : ℝ) (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((nchar K s x : ℂˣ) : ℂ) = (((ideleNorm K x) ^ s : ℝ) : ℂ) := rfl

theorem nchar_eq_one_of_ideleNorm_eq_one (s : ℝ) {x : (AdeleRing (𝓞 K) K)ˣ}
    (hx : ideleNorm K x = 1) : nchar K s x = 1 :=
  Units.ext (by rw [coe_nchar_apply, hx, Real.one_rpow, Complex.ofReal_one, Units.val_one])

theorem chiDet_nchar_apply (s : ℝ) (g : AdelicGL2 (𝓞 K) K) :
    chiDet (𝓞 K) K (nchar K s) g
      = (((ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ s : ℝ) : ℂ) := rfl

theorem norm_chiDet_nchar (s : ℝ) (g : AdelicGL2 (𝓞 K) K) :
    ‖chiDet (𝓞 K) K (nchar K s) g‖ = (ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ s := by
  rw [chiDet_nchar_apply, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (ideleNorm_pos _).le s)]

theorem chiDet_mul (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (x y : AdelicGL2 (𝓞 K) K) :
    chiDet (𝓞 K) K η (x * y) = chiDet (𝓞 K) K η x * chiDet (𝓞 K) K η y := by
  simp only [chiDet, map_mul, Units.val_mul]

theorem continuous_chiDet_nchar (s : ℝ) : Continuous (chiDet (𝓞 K) K (nchar K s)) := by
  show Continuous fun g : AdelicGL2 (𝓞 K) K =>
    (((ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ s : ℝ) : ℂ)
  exact Complex.continuous_ofReal.comp
    ((NumberField.TateGlobal.continuous_ideleNorm_det K).rpow_const
      fun g => Or.inl (ideleNorm_pos _).ne')

theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, diagOne_coe_apply,
    diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply]
  simp

theorem det_unipotentGL2 (x : AdeleRing (𝓞 K) K) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of,
    Units.val_one]
  ring

theorem det_heckeGen (v : HeightOneSpectrum (𝓞 K)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v) = uniformizerIdele K v := by
  show Matrix.GeneralLinearGroup.det
      (diagOne (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (uniformizerUnit K v)))) = _
  rw [det_diagOne]
  rfl

theorem isIdeleClassChar_nchar (s : ℝ) : IsIdeleClassChar (𝓞 K) K (nchar K s) := by
  intro u
  apply nchar_eq_one_of_ideleNorm_eq_one
  have h := AutomorphicForm.ideleNorm_det_globalPoints (F := K) (diagOne u)
  rwa [globalPoints, Matrix.GeneralLinearGroup.map_det, det_diagOne] at h

theorem coe_nchar_uniformizerIdele (s : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    ((nchar K s (uniformizerIdele K v) : ℂˣ) : ℂ)
      = (((Ideal.absNorm v.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [coe_nchar_apply, NumberField.TateGlobal.ideleNorm_uniformizerIdele K v,
    Real.inv_rpow (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]

theorem chiDet_nchar_heckeGen (s : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    chiDet (𝓞 K) K (nchar K s) (heckeGen (𝓞 K) K v)
      = ((nchar K s (uniformizerIdele K v) : ℂˣ) : ℂ) := by
  unfold chiDet
  rw [det_heckeGen]

theorem ideleNorm_det_eq_one {k : AdelicGL2 (𝓞 K) K} (harch : glArch (𝓞 K) K k = 1)
    (hfin : glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det k) = 1 := by
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K k hfin]
  refine Finset.prod_eq_one fun w _ => ?_
  simp only [archDetNorm, harch, map_one, Units.val_one, Matrix.det_one, norm_one, one_pow]

theorem chiDet_nchar_eq_one (s : ℝ) {k : AdelicGL2 (𝓞 K) K} (harch : glArch (𝓞 K) K k = 1)
    (hfin : glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K) :
    chiDet (𝓞 K) K (nchar K s) k = 1 := by
  unfold chiDet
  rw [nchar_eq_one_of_ideleNorm_eq_one s (ideleNorm_det_eq_one harch hfin), Units.val_one]

theorem glFin_mem_finiteIntegralGL2_of_mem_levelOne {N : Ideal (𝓞 K)} {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ levelOne (𝓞 K) K N) : glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K := by
  have h := mem_finiteLevelOne_iff.mp (mem_levelOne_iff.mp hk)
  exact mem_finiteIntegralGL2_iff.mpr ⟨h.1.integral, h.2.integral⟩

theorem chiDet_nchar_eq_one_of_mem_U (s : ℝ) {N : Ideal (𝓞 K)} {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) :
    chiDet (𝓞 K) K (nchar K s) k = 1 :=
  chiDet_nchar_eq_one s ((mem_finiteAdelicGL2Subgroup_iff K k).mp (Subgroup.mem_inf.mp hk).2)
    (glFin_mem_finiteIntegralGL2_of_mem_levelOne (Subgroup.mem_inf.mp hk).1)

theorem chiDet_nchar_mul_of_mem_U (s : ℝ) {N : Ideal (𝓞 K)} {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (g : AdelicGL2 (𝓞 K) K) :
    chiDet (𝓞 K) K (nchar K s) (g * k) = chiDet (𝓞 K) K (nchar K s) g := by
  rw [chiDet_mul, chiDet_nchar_eq_one_of_mem_U s hk, mul_one]

theorem isKfSmooth_chiDet_nchar (s : ℝ) : IsKfSmooth K (chiDet (𝓞 K) K (nchar K s)) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup]
  refine ⟨(levelZero (𝓞 K) K ⊤).subgroupOf (finiteAdelicGL2Subgroup K), ?_, ?_⟩
  · exact (isOpen_levelZero (𝓞 K) K (N := (⊤ : Ideal (𝓞 K))) (by simp)).preimage
      continuous_subtype_val
  · intro k hk
    refine RightTranslationFn.ext fun g => ?_
    rw [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk,
      chiDet_mul, chiDet_nchar_eq_one s ((mem_finiteAdelicGL2Subgroup_iff K _).mp k.2)
        (Subgroup.mem_subgroupOf.mp hk), mul_one]

theorem chiDet_unipotentGL2_mul (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (x : AdeleRing (𝓞 K) K)
    (g : AdelicGL2 (𝓞 K) K) :
    chiDet (𝓞 K) K η (unipotentGL2 x * g) = chiDet (𝓞 K) K η g := by
  simp only [chiDet, map_mul, det_unipotentGL2, map_one, one_mul]

theorem isCuspidalFn_fnTwist {mQ : MeasurableSpace (AdeleRing (𝓞 K) K)}
    (ν : Measure (AdeleRing (𝓞 K) K)) (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsCuspidalFn ν unipotentGL2 φ) :
    IsCuspidalFn ν unipotentGL2 (fnTwist K η φ) := by
  intro g
  have h0 := hφ g
  simp only [constantTerm, constantTermIntegrand, fnTwist_apply, chiDet_unipotentGL2_mul] at h0 ⊢
  rw [integral_const_mul, h0, mul_zero]

theorem heckeCosetSum_fnTwist_nchar (s : ℝ) {N : Ideal (𝓞 K)} {v : HeightOneSpectrum (𝓞 K)}
    {n : ℕ} {reps : Fin n → AdelicGL2 (𝓞 K) K}
    (hreps : IsHeckeCosetSystem (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (heckeGen (𝓞 K) K v) reps)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) :
    heckeCosetSum K reps (fnTwist K (nchar K s) φ) g
      = ((nchar K s (uniformizerIdele K v) : ℂˣ) : ℂ) * chiDet (𝓞 K) K (nchar K s) g
          * heckeCosetSum K reps φ g := by
  unfold heckeCosetSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨a, ha, b, hb, hab⟩ := HeckePair.mem_doubleCoset_iff.mp (hreps.mem_doubleCoset i)
  have hdet : chiDet (𝓞 K) K (nchar K s) (reps i)
      = ((nchar K s (uniformizerIdele K v) : ℂˣ) : ℂ) := by
    rw [← hab, chiDet_mul, chiDet_mul, chiDet_nchar_eq_one_of_mem_U s ha,
      chiDet_nchar_eq_one_of_mem_U s hb, one_mul, mul_one, chiDet_nchar_heckeGen]
  rw [fnTwist_apply, chiDet_mul, hdet]
  ring

theorem fnTwist_centralScalar_mul (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} {z : (AdeleRing (𝓞 K) K)ˣ} {b : ℂ}
    (hφ : ∀ g, φ (centralScalar (𝓞 K) K z * g) = b * φ g) (g : AdelicGL2 (𝓞 K) K) :
    fnTwist K η φ (centralScalar (𝓞 K) K z * g)
      = ((η z : ℂˣ) : ℂ) ^ 2 * b * fnTwist K η φ g := by
  rw [fnTwist_apply, fnTwist_apply, chiDet_centralScalar_mul, hφ g]
  ring

variable (K)
variable (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))

abbrev window : Set (AdelicGL2 (𝓞 K) K) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂

abbrev pins : CarrierPins K :=
  productionPinsOf K (window K c u d₁ d₂ T)
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

theorem window_measurableSet :
    (letI := (pins K c u d₁ d₂ T).mS; MeasurableSet (pins K c u d₁ d₂ T).D) := by
  letI := glBorel (Fin 2) (𝓞 K) K
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  show MeasurableSet (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
  refine Finset.measurableSet_biUnion T fun x _ => ?_
  rw [Set.image_mul_right]
  exact (continuous_id.mul continuous_const).measurable (measurableSet_centreCutSiegelSet c u d₁ d₂)

variable {K c u d₁ d₂ T}

theorem ideleNorm_det_pinch_of_mem_centreCut (hd₁ : 0 < d₁) {y : AdelicGL2 (𝓞 K) K}
    (hy : y ∈ centreCutSiegelSet K c u d₁ d₂) :
    (∏ w : InfinitePlace K, d₁ ^ w.mult) ≤ ideleNorm K (Matrix.GeneralLinearGroup.det y) ∧
      ideleNorm K (Matrix.GeneralLinearGroup.det y) ≤ ∏ w : InfinitePlace K, (max d₁ d₂) ^ w.mult := by
  obtain ⟨hfin, -, -, hdet⟩ := hy
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K y hfin]
  refine ⟨Finset.prod_le_prod (fun w _ => pow_nonneg hd₁.le _)
      fun w _ => pow_le_pow_left₀ hd₁.le (hdet w).1 _,
    Finset.prod_le_prod (fun w _ => pow_nonneg (archDetNorm_pos w y).le _)
      fun w _ => pow_le_pow_left₀ (archDetNorm_pos w y).le ((hdet w).2.trans (le_max_right _ _)) _⟩

theorem rpow_le_of_pinch {m M x : ℝ} (hm : 0 < m) (hmx : m ≤ x) (hxM : x ≤ M) (s : ℝ) :
    x ^ s ≤ m ^ s + M ^ s := by
  have hx : 0 < x := hm.trans_le hmx
  have hM : 0 ≤ M := hx.le.trans hxM
  rcases le_or_gt 0 s with hs | hs
  · calc x ^ s ≤ M ^ s := Real.rpow_le_rpow hx.le hxM hs
      _ ≤ m ^ s + M ^ s := le_add_of_nonneg_left (Real.rpow_nonneg hm.le s)
  · calc x ^ s ≤ m ^ s := Real.rpow_le_rpow_of_nonpos hm hmx hs.le
      _ ≤ m ^ s + M ^ s := le_add_of_nonneg_right (Real.rpow_nonneg hM s)

def windowBound (s : ℝ) : ℝ :=
  ((∏ w : InfinitePlace K, d₁ ^ w.mult) ^ s + (∏ w : InfinitePlace K, (max d₁ d₂) ^ w.mult) ^ s)
    * ∑ x ∈ T, (ideleNorm K (Matrix.GeneralLinearGroup.det x)) ^ s

theorem norm_chiDet_nchar_le_of_mem_window (hd₁ : 0 < d₁) (s : ℝ) {g : AdelicGL2 (𝓞 K) K}
    (hg : g ∈ window K c u d₁ d₂ T) :
    ‖chiDet (𝓞 K) K (nchar K s) g‖ ≤ windowBound (K := K) (d₁ := d₁) (d₂ := d₂) (T := T) s := by
  rw [norm_chiDet_nchar]
  obtain ⟨x, hxT, hgx⟩ := Set.mem_iUnion₂.mp hg
  obtain ⟨y, hy, rfl⟩ := hgx
  show (ideleNorm K (Matrix.GeneralLinearGroup.det (y * x))) ^ s ≤ _
  have hm : 0 < ∏ w : InfinitePlace K, d₁ ^ w.mult := Finset.prod_pos fun w _ => pow_pos hd₁ _
  have hM : 0 < ∏ w : InfinitePlace K, (max d₁ d₂) ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (hd₁.trans_le (le_max_left _ _)) _
  obtain ⟨h1, h2⟩ := ideleNorm_det_pinch_of_mem_centreCut (c := c) (u := u) hd₁ hy
  rw [map_mul, ideleNorm_mul, Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le]
  refine mul_le_mul (rpow_le_of_pinch hm h1 h2 s) ?_ (Real.rpow_nonneg (ideleNorm_pos _).le s)
    (add_nonneg (Real.rpow_nonneg hm.le s) (Real.rpow_nonneg hM.le s))
  exact Finset.single_le_sum (f := fun x => (ideleNorm K (Matrix.GeneralLinearGroup.det x)) ^ s)
    (fun x _ => Real.rpow_nonneg (ideleNorm_pos _).le s) hxT

variable (K c u d₁ d₂ T)

theorem memLp_fnTwist_nchar (hd₁ : 0 < d₁) (s : ℝ) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφc : Continuous φ)
    (hφ : letI := (pins K c u d₁ d₂ T).mS;
      MemLp φ 2 ((pins K c u d₁ d₂ T).μ.restrict (pins K c u d₁ d₂ T).D)) :
    letI := (pins K c u d₁ d₂ T).mS;
    MemLp (fnTwist K (nchar K s) φ) 2 ((pins K c u d₁ d₂ T).μ.restrict (pins K c u d₁ d₂ T).D) := by
  letI := glBorel (Fin 2) (𝓞 K) K
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  have hcont : Continuous (fnTwist K (nchar K s) φ) := (continuous_chiDet_nchar s).mul hφc
  refine MemLp.of_le_mul (c := windowBound (K := K) (d₁ := d₁) (d₂ := d₂) (T := T) s) hφ
    hcont.aestronglyMeasurable ?_
  refine (ae_restrict_iff' (window_measurableSet K c u d₁ d₂ T)).mpr
    (Filter.Eventually.of_forall fun g hg => ?_)
  rw [fnTwist_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_chiDet_nchar_le_of_mem_window (c := c) (u := u) hd₁ s hg) (norm_nonneg _)

def twistRealization (hd₁ : 0 < d₁) (s : ℝ) (χ : HeightOneSpectrum (𝓞 K) → ℂ)
    (hχ : ∀ v, χ v = ((nchar K s (uniformizerIdele K v) : ℂˣ) : ℂ))
    (Φ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K (pins K c u d₁ d₂ T) Φ.toRawCentral) (hR : Continuous R.toFun) :
    SmoothCuspRealizationAt K (pins K c u d₁ d₂ T) (Φ.twist χ).toRawCentral where
  toFun := fnTwist K (nchar K s) R.toFun
  exists_ne_zero := by
    obtain ⟨g, hg⟩ := R.exists_ne_zero
    exact ⟨g, by rw [fnTwist_apply]; exact mul_ne_zero (Units.ne_zero _) hg⟩
  centralChar := twistedCentralChar K (pins K c u d₁ d₂ T).Z R.centralChar (nchar K s)
  smoothCusp := by
    letI := (pins K c u d₁ d₂ T).mS
    obtain ⟨⟨hauto, hcusp⟩, hkf⟩ := R.smoothCusp
    have h2 := (lsXiMemberAt_iff (𝓞 K) K (pins K c u d₁ d₂ T).μ (pins K c u d₁ d₂ T).Z
      R.centralChar (pins K c u d₁ d₂ T).D R.toFun).mp hauto
    have hlsxi := isLsXiFunction_fnTwist K (nchar K s) (isIdeleClassChar_nchar s) h2.1
    have hL2 := memLp_fnTwist_nchar K c u d₁ d₂ T hd₁ s hR h2.2
    have hcusp' := isCuspidalFn_fnTwist (pins K c u d₁ d₂ T).ν (nchar K s) hcusp
    have hkf' := isKfSmooth_fnTwist K (nchar K s) (isKfSmooth_chiDet_nchar s) hkf
    exact ⟨⟨(lsXiMemberAt_iff (𝓞 K) K (pins K c u d₁ d₂ T).μ (pins K c u d₁ d₂ T).Z
        (twistedCentralChar K (pins K c u d₁ d₂ T).Z R.centralChar (nchar K s))
        (pins K c u d₁ d₂ T).D (fnTwist K (nchar K s) R.toFun)).mpr ⟨hlsxi, hL2⟩, hcusp'⟩, hkf'⟩
  level_invariant := fun g k hk => by
    rw [fnTwist_apply, fnTwist_apply, R.level_invariant g k hk, chiDet_nchar_mul_of_mem_U s hk]
  exceptionalSet := R.exceptionalSet
  hecke_eigen := fun v hv => by
    obtain ⟨reps, hreps, hsum⟩ := R.hecke_eigen v hv
    have hreps' : IsHeckeCosetSystem (levelOne (𝓞 K) K Φ.level ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) reps := hreps
    refine ⟨reps, hreps, fun g => ?_⟩
    rw [heckeCosetSum_fnTwist_nchar s hreps' R.toFun g, hsum g, fnTwist_apply,
      HeckeEigensystem.toRawCentral_a, HeckeEigensystem.toRawCentral_a,
      HeckeEigensystem.twist_a, hχ v]
    ring
  central_eigen := fun v hv g => by
    have h : ∀ g', R.toFun (centralScalar (𝓞 K) K
        (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * g')
          = Φ.toRawCentral.b v * R.toFun g' := fun g' => R.central_eigen v hv g'
    show fnTwist K (nchar K s) R.toFun (centralScalar (𝓞 K) K
        (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * g)
      = (Φ.twist χ).toRawCentral.b v * fnTwist K (nchar K s) R.toFun g
    rw [fnTwist_centralScalar_mul (nchar K s) h g, det_heckeGen,
      HeckeEigensystem.toRawCentral_b, HeckeEigensystem.toRawCentral_b,
      HeckeEigensystem.twist_b, hχ v]
    ring

theorem continuous_twistRealization (hd₁ : 0 < d₁) (s : ℝ) (χ : HeightOneSpectrum (𝓞 K) → ℂ)
    (hχ : ∀ v, χ v = ((nchar K s (uniformizerIdele K v) : ℂˣ) : ℂ))
    (Φ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K (pins K c u d₁ d₂ T) Φ.toRawCentral) (hR : Continuous R.toFun) :
    Continuous (twistRealization K c u d₁ d₂ T hd₁ s χ hχ Φ R hR).toFun := by
  show Continuous (fnTwist K (nchar K s) R.toFun)
  exact (continuous_chiDet_nchar s).mul hR

end TwistRpow

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd₁ : 0 < d₁)
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
    (t : ℝ) :
    ∃ R' : SmoothCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
        (Θ.twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).toRawCentral,
      IsGenuineCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
        (Θ.twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).toRawCentral R' ∧
      R'.exceptionalSet = R.exceptionalSet ∧
      ∀ g : AdelicGL2 (𝓞 K) K,
        R'.toFun g = ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * R.toFun g := by
  refine ⟨TwistRpow.twistRealization K c u d₁ d₂ T hd₁ t _
      (fun v => (TwistRpow.coe_nchar_uniformizerIdele t v).symm) Θ R hR,
    TwistRpow.continuous_twistRealization K c u d₁ d₂ T hd₁ t _
      (fun v => (TwistRpow.coe_nchar_uniformizerIdele t v).symm) Θ R hR, rfl, fun g => ?_⟩
  show fnTwist K (TwistRpow.nchar K t) R.toFun g = _
  rw [fnTwist_apply, TwistRpow.chiDet_nchar_apply]

end S_AutomorphicForm_SmoothCuspRealizationAt_exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
end P2MW
export P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul (solution)
