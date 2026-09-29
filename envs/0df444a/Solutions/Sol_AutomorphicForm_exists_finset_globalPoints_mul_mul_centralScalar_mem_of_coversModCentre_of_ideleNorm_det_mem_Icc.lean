-- Prove2me | solution 1 for AutomorphicForm.exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d28a8ddd-8613-555e-a820-e4f1ec4b1339

import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicVolume NumberField.TateGlobal

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped NNReal Pointwise

noncomputable section

namespace K1aSlabCover

variable {F : Type} [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔾" => AdelicGL2 (𝓞 F) F

theorem globalPoints_apply (γ : GL (Fin 2) F) (i j : Fin 2) :
    ((globalPoints (𝓞 F) F γ : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) i j =
      algebraMap F 𝔸 ((γ : Matrix (Fin 2) (Fin 2) F) i j) := rfl

theorem globalPoints_injective : Function.Injective (globalPoints (𝓞 F) F) := by
  intro a b h
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have := congrArg (fun g : 𝔾 => (g : Matrix (Fin 2) (Fin 2) 𝔸) i j) h
  simp only [globalPoints_apply] at this
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 F) F this

theorem det_globalPoints (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ) =
      Units.map (algebraMap F 𝔸).toMonoidHom (Matrix.GeneralLinearGroup.det γ) := by
  unfold globalPoints
  rw [Matrix.GeneralLinearGroup.map_det]
  rfl

theorem det_centralScalar (z : 𝔸ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z) = z ^ 2 := by
  show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z ^ 2
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem globalPoints_scalar (a : Fˣ) :
    globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      centralScalar (𝓞 F) F (Units.map (algebraMap F 𝔸).toMonoidHom a) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [globalPoints_apply]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq]
    show algebraMap F 𝔸 ((Matrix.scalar (Fin 2) (a : F)) i i) = _
    simp
  · rw [centralScalar_apply_ne _ h]
    show algebraMap F 𝔸 ((Matrix.scalar (Fin 2) (a : F)) i j) = _
    simp [h]

theorem ideleNorm_principal (a : Fˣ) :
    ideleNorm F (Units.map (algebraMap F 𝔸).toMonoidHom a) = 1 := by
  unfold ideleNorm
  rw [@NumberField.AdeleRing.distribHaarChar_algebraMap F _ _ (adeleBorel (𝓞 F) F)
    (borelSpace_adeleBorel (𝓞 F) F) a]
  simp

theorem ideleNorm_det_globalPoints_mul (γ : GL (Fin 2) F) (g : 𝔾) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ * g)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, ideleNorm_mul, det_globalPoints, ideleNorm_principal, one_mul]

theorem ideleNorm_det_centralScalar_mul (z : 𝔸ˣ) (g : 𝔾) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * g)) =
      ideleNorm F z ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, ideleNorm_mul, det_centralScalar, sq, sq, ideleNorm_mul]

theorem ideleNorm_det_mul (g h : 𝔾) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (g * h)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) *
        ideleNorm F (Matrix.GeneralLinearGroup.det h) := by
  rw [map_mul, ideleNorm_mul]

theorem ideleNorm_det_pos (g : 𝔾) : 0 < ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
  ideleNorm_pos _

theorem archComponent_archCentralUnit_of_ne (w₀ : InfinitePlace F) (a : (w₀.Completion)ˣ)
    {w : InfinitePlace F} (hw : w ≠ w₀) :
    archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F w₀ a))) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [archComponent_apply, glArch_apply, Units.val_one]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, Matrix.one_apply_eq]
    exact archCentralUnit_fst_of_ne w₀ a hw
  · rw [centralScalar_apply_ne _ h, Matrix.one_apply_ne h]
    rfl

theorem archDetNorm_one (w : InfinitePlace F) : archDetNorm w (1 : 𝔾) = 1 := by
  unfold archDetNorm
  rw [map_one, map_one, Units.val_one, Matrix.det_one, norm_one]

theorem archDetNorm_archCentralUnit_self (w₀ : InfinitePlace F) (a : (w₀.Completion)ˣ) :
    archDetNorm w₀ (centralScalar (𝓞 F) F (archCentralUnit F w₀ a)) =
      ‖(a : w₀.Completion)‖ * ‖(a : w₀.Completion)‖ := by
  have := archDetNorm_centralScalar_mul w₀ a (1 : 𝔾)
  rw [mul_one, archDetNorm_one, mul_one] at this
  exact this

theorem archDetNorm_archCentralUnit_of_ne (w₀ : InfinitePlace F) (a : (w₀.Completion)ˣ)
    {w : InfinitePlace F} (hw : w ≠ w₀) :
    archDetNorm w (centralScalar (𝓞 F) F (archCentralUnit F w₀ a)) = 1 := by
  unfold archDetNorm
  rw [archComponent_archCentralUnit_of_ne w₀ a hw, Units.val_one, Matrix.det_one, norm_one]

theorem ideleNorm_archCentralUnit (w₀ : InfinitePlace F) (a : (w₀.Completion)ˣ) :
    ideleNorm F (archCentralUnit F w₀ a) = ‖(a : w₀.Completion)‖ ^ w₀.mult := by
  set X : 𝔾 := centralScalar (𝓞 F) F (archCentralUnit F w₀ a) with hX
  have hint : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F := by
    rw [hX, glFin_centralScalar_archCentralUnit]
    exact Subgroup.one_mem _
  have hcard := NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F X hint
  rw [hX, det_centralScalar, sq, ideleNorm_mul] at hcard
  have hprod : ∏ w : InfinitePlace F, archDetNorm w X ^ w.mult =
      (‖(a : w₀.Completion)‖ * ‖(a : w₀.Completion)‖) ^ w₀.mult := by
    rw [Finset.prod_eq_single w₀]
    · rw [hX, archDetNorm_archCentralUnit_self]
    · intro w _ hw
      rw [hX, archDetNorm_archCentralUnit_of_ne w₀ a hw, one_pow]
    · intro hw; exact absurd (Finset.mem_univ w₀) hw
  rw [hprod] at hcard
  have h1 : ideleNorm F (archCentralUnit F w₀ a) ^ 2 = (‖(a : w₀.Completion)‖ ^ w₀.mult) ^ 2 := by
    rw [sq, hcard]; ring
  have hpos : 0 ≤ ideleNorm F (archCentralUnit F w₀ a) := (ideleNorm_pos _).le
  exact (pow_left_inj₀ hpos (by positivity) two_ne_zero).mp h1

def realEmb (w : InfinitePlace F) : ℝ →+* w.Completion := by
  classical
  exact if hw : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
  else ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm.toRingHom).comp Complex.ofRealHom

theorem extensionEmbedding_realEmb (w : InfinitePlace F) (r : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w (realEmb w r) = (r : ℂ) := by
  unfold realEmb
  split_ifs with hw
  · rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
      ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hw, RingEquiv.apply_symm_apply]
  · rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      ← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply
        (InfinitePlace.not_isReal_iff_isComplex.mp hw), RingEquiv.apply_symm_apply]
    rfl

theorem norm_realEmb (w : InfinitePlace F) (r : ℝ) : ‖realEmb w r‖ = |r| := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
    extensionEmbedding_realEmb, Complex.norm_real, Real.norm_eq_abs]

theorem realEmb_ne_zero (w : InfinitePlace F) {r : ℝ} (hr : r ≠ 0) : realEmb w r ≠ 0 := by
  intro h
  have := norm_realEmb w r
  rw [h, norm_zero] at this
  exact hr (abs_eq_zero.mp this.symm)

def realUnit (w : InfinitePlace F) (r : ℝ) (hr : r ≠ 0) : (w.Completion)ˣ :=
  Units.mk0 (realEmb w r) (realEmb_ne_zero w hr)

def sec (w₀ : InfinitePlace F) (r : ℝ) (hr : 0 < r) : 𝔸ˣ :=
  archCentralUnit F w₀ (realUnit w₀ r hr.ne')

theorem ideleNorm_sec (w₀ : InfinitePlace F) (r : ℝ) (hr : 0 < r) :
    ideleNorm F (sec w₀ r hr) = r ^ w₀.mult := by
  unfold sec realUnit
  rw [ideleNorm_archCentralUnit, Units.val_mk0, norm_realEmb, abs_of_pos hr]

theorem prod_pow_mult_le {a b : InfinitePlace F → ℝ} (h0 : ∀ w, 0 ≤ a w) (h : ∀ w, a w ≤ b w) :
    ∏ w : InfinitePlace F, a w ^ w.mult ≤ ∏ w : InfinitePlace F, b w ^ w.mult :=
  Finset.prod_le_prod (fun w _ => pow_nonneg (h0 w) _)
    (fun w _ => pow_le_pow_left₀ (h0 w) (h w) _)

theorem ideleNorm_det_siegel {c u d₁ d₂ : ℝ} (hd₁ : 0 < d₁) {s : 𝔾}
    (hs : s ∈ centreCutSiegelSet F c u d₁ d₂) :
    d₁ ^ (∑ w : InfinitePlace F, w.mult) ≤ ideleNorm F (Matrix.GeneralLinearGroup.det s) ∧
      ideleNorm F (Matrix.GeneralLinearGroup.det s) ≤ d₂ ^ (∑ w : InfinitePlace F, w.mult) := by
  have hint := (mem_centreCutSiegelSet_iff.mp hs).1
  have hdet := (mem_centreCutSiegelSet_iff.mp hs).2.2.2
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F s hint,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  exact ⟨prod_pow_mult_le (fun _ => hd₁.le) fun w => (hdet w).1,
    prod_pow_mult_le (fun w => (archDetNorm_pos w s).le) fun w => (hdet w).2⟩

theorem ideleNorm_inv (z : 𝔸ˣ) : ideleNorm F z⁻¹ = (ideleNorm F z)⁻¹ := by
  unfold ideleNorm; rw [map_inv, NNReal.coe_inv]

def goodAdele (δ : ℝ) : Set 𝔸 :=
  {a | a.2 ∈ integralFiniteAdeles (𝓞 F) F ∧ ∀ w : InfinitePlace F, ‖a.1 w‖ < δ}

theorem isOpen_goodAdele (δ : ℝ) : IsOpen (goodAdele (F := F) δ) := by
  have h1 : IsOpen {a : 𝔸 | a.2 ∈ integralFiniteAdeles (𝓞 F) F} :=
    (isOpen_integralFiniteAdeles (𝓞 F) F).preimage continuous_snd
  have h2 : IsOpen {a : 𝔸 | ∀ w : InfinitePlace F, ‖a.1 w‖ < δ} := by
    have : {a : 𝔸 | ∀ w : InfinitePlace F, ‖a.1 w‖ < δ} = ⋂ w : InfinitePlace F, {a : 𝔸 | ‖a.1 w‖ < δ} := by
      ext a; simp [Set.mem_iInter]
    rw [this]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt (continuous_norm.comp ((continuous_apply w).comp continuous_fst)) continuous_const
  exact h1.inter h2

def Rδ (δ : ℝ) : Set 𝔸ˣ :=
  {r | ((r : 𝔸ˣ) : 𝔸) ∈ goodAdele δ ∧ ((r⁻¹ : 𝔸ˣ) : 𝔸) ∈ goodAdele δ}

theorem isOpen_Rδ (δ : ℝ) : IsOpen (Rδ (F := F) δ) :=
  ((isOpen_goodAdele δ).preimage Units.continuous_val).inter
    ((isOpen_goodAdele δ).preimage Units.continuous_coe_inv)

theorem inv_mem_Rδ {δ : ℝ} {r : 𝔸ˣ} (hr : r ∈ Rδ δ) : r⁻¹ ∈ Rδ δ :=
  ⟨hr.2, by rw [inv_inv]; exact hr.1⟩

theorem fst_one_apply (w : InfinitePlace F) : (1 : 𝔸).1 w = 1 := rfl

theorem fst_mul_apply (a b : 𝔸) (w : InfinitePlace F) : (a * b).1 w = a.1 w * b.1 w := rfl

theorem snd_mul (a b : 𝔸) : (a * b).2 = a.2 * b.2 := rfl

theorem one_mem_Rδ {δ : ℝ} (hδ : 1 < δ) : (1 : 𝔸ˣ) ∈ Rδ δ := by
  have h1 : ((1 : 𝔸ˣ) : 𝔸) ∈ goodAdele δ := by
    refine ⟨fun v => ?_, fun w => ?_⟩
    · exact one_mem _
    · rw [Units.val_one, fst_one_apply, norm_one]; exact hδ
  exact ⟨h1, by rw [inv_one]; exact h1⟩

theorem norm_fst_mul_norm_fst_inv (r : 𝔸ˣ) (w : InfinitePlace F) :
    ‖((r : 𝔸ˣ) : 𝔸).1 w‖ * ‖((r⁻¹ : 𝔸ˣ) : 𝔸).1 w‖ = 1 := by
  rw [← norm_mul, ← fst_mul_apply, Units.mul_inv, fst_one_apply, norm_one]

theorem norm_fst_ne_zero (r : 𝔸ˣ) (w : InfinitePlace F) : ((r : 𝔸ˣ) : 𝔸).1 w ≠ 0 := by
  intro h
  have := norm_fst_mul_norm_fst_inv r w
  rw [h, norm_zero, zero_mul] at this
  exact zero_ne_one this

theorem inv_lt_norm_fst_of_mem_Rδ {δ : ℝ} (hδ : 0 < δ) {r : 𝔸ˣ} (hr : r ∈ Rδ δ)
    (w : InfinitePlace F) : δ⁻¹ < ‖((r : 𝔸ˣ) : 𝔸).1 w‖ := by
  have hprod := norm_fst_mul_norm_fst_inv r w
  have hb : ‖((r⁻¹ : 𝔸ˣ) : 𝔸).1 w‖ < δ := (hr.2.2 w)
  have hbpos : 0 < ‖((r⁻¹ : 𝔸ˣ) : 𝔸).1 w‖ := norm_pos_iff.mpr (norm_fst_ne_zero r⁻¹ w)
  have ha : ‖((r : 𝔸ˣ) : 𝔸).1 w‖ = (‖((r⁻¹ : 𝔸ˣ) : 𝔸).1 w‖)⁻¹ :=
    eq_inv_of_mul_eq_one_left hprod
  rw [ha]
  exact (inv_lt_inv₀ hδ hbpos).mpr hb

theorem archComponent_centralScalar_apply (r : 𝔸ˣ) (w : InfinitePlace F) (i j : Fin 2) :
    ((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F r)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j =
      if i = j then ((r : 𝔸ˣ) : 𝔸).1 w else 0 := by
  rw [archComponent_apply, glArch_apply]
  by_cases h : i = j
  · subst h; rw [centralScalar_apply_eq, if_pos rfl]
  · rw [centralScalar_apply_ne _ h, if_neg h]; rfl

theorem glFin_centralScalar_mem {r : 𝔸ˣ} (h1 : ((r : 𝔸ˣ) : 𝔸).2 ∈ integralFiniteAdeles (𝓞 F) F)
    (h2 : ((r⁻¹ : 𝔸ˣ) : 𝔸).2 ∈ integralFiniteAdeles (𝓞 F) F) :
    glFin (𝓞 F) F (centralScalar (𝓞 F) F r) ∈ finiteIntegralGL2 (𝓞 F) F := by
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j
    rw [glFin_apply]
    by_cases h : i = j
    · subst h; rw [centralScalar_apply_eq]; exact h1
    · rw [centralScalar_apply_ne _ h]; exact zero_mem_integralFiniteAdeles
  · intro i j
    rw [← map_inv, glFin_apply, ← map_inv]
    by_cases h : i = j
    · subst h; rw [centralScalar_apply_eq]; exact h2
    · rw [centralScalar_apply_ne _ h]; exact zero_mem_integralFiniteAdeles

theorem localHeight_centralScalar_mul (r : 𝔸ˣ) (g : 𝔾) (w : InfinitePlace F) :
    localHeight (archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F r * g))) =
      localHeight (archComponent F w (glArch (𝓞 F) F g)) := by
  rw [map_mul, map_mul]
  refine localHeight_scalar_entries_mul (norm_fst_ne_zero r w) ?_ ?_ ?_ ?_ _
  · rw [archComponent_centralScalar_apply, if_pos rfl]
  · rw [archComponent_centralScalar_apply, if_neg (by decide)]
  · rw [archComponent_centralScalar_apply, if_neg (by decide)]
  · rw [archComponent_centralScalar_apply, if_pos rfl]

theorem xWindowSq_centralScalar_mul (r : 𝔸ˣ) (g : 𝔾) (w : InfinitePlace F) :
    xWindowSq (archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F r * g))) =
      xWindowSq (archComponent F w (glArch (𝓞 F) F g)) := by
  rw [map_mul, map_mul]
  refine xWindowSq_scalar_entries_mul (norm_fst_ne_zero r w) ?_ ?_ ?_ ?_ _
  · rw [archComponent_centralScalar_apply, if_pos rfl]
  · rw [archComponent_centralScalar_apply, if_neg (by decide)]
  · rw [archComponent_centralScalar_apply, if_neg (by decide)]
  · rw [archComponent_centralScalar_apply, if_pos rfl]

theorem archDetNorm_centralScalar_mul' (r : 𝔸ˣ) (g : 𝔾) (w : InfinitePlace F) :
    archDetNorm w (centralScalar (𝓞 F) F r * g) = ‖((r : 𝔸ˣ) : 𝔸).1 w‖ ^ 2 * archDetNorm w g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul, Matrix.det_fin_two,
    archComponent_centralScalar_apply, archComponent_centralScalar_apply,
    archComponent_centralScalar_apply, archComponent_centralScalar_apply]
  simp [norm_mul, sq]

theorem centralScalar_mul_mem_siegel {δ : ℝ} (hδ : 0 < δ) {r : 𝔸ˣ} (hr : r ∈ Rδ δ)
    {c u d₁ d₂ : ℝ} (hd₁ : 0 ≤ d₁) {s : 𝔾} (hs : s ∈ centreCutSiegelSet F c u d₁ d₂) :
    centralScalar (𝓞 F) F r * s ∈ centreCutSiegelSet F c u (d₁ / δ ^ 2) (d₂ * δ ^ 2) := by
  obtain ⟨hK, hh, hx, hdet⟩ := mem_centreCutSiegelSet_iff.mp hs
  refine mem_centreCutSiegelSet_iff.mpr ⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩
  · rw [map_mul]
    exact Subgroup.mul_mem _ (glFin_centralScalar_mem hr.1.1 hr.2.1) hK
  · rw [localHeight_centralScalar_mul]; exact hh w
  · rw [xWindowSq_centralScalar_mul]; exact hx w
  · rw [archDetNorm_centralScalar_mul']
    set a := ‖((r : 𝔸ˣ) : 𝔸).1 w‖ with ha
    have ha1 : a < δ := hr.1.2 w
    have ha2 : δ⁻¹ < a := inv_lt_norm_fst_of_mem_Rδ hδ hr w
    have ha0 : 0 ≤ a := norm_nonneg _
    have hA := hdet w
    have hApos : 0 < archDetNorm w s := archDetNorm_pos w s
    constructor
    · have h1 : d₁ / δ ^ 2 = (δ⁻¹) ^ 2 * d₁ := by field_simp
      rw [h1]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) ha2.le 2) hA.1 hd₁ (by positivity)
    · rw [mul_comm d₂]
      exact mul_le_mul (pow_le_pow_left₀ ha0 ha1.le 2) hA.2 hApos.le (by positivity)

def archIdele (β : ∀ w : InfinitePlace F, (w.Completion)ˣ) : 𝔸ˣ where
  val := (fun w => (β w : w.Completion), 1)
  inv := (fun w => ((β w)⁻¹ : (w.Completion)ˣ), 1)
  val_inv := Prod.ext (funext fun w => Units.mul_inv (β w)) (one_mul 1)
  inv_val := Prod.ext (funext fun w => Units.inv_mul (β w)) (one_mul 1)

theorem archIdele_fst (β : ∀ w : InfinitePlace F, (w.Completion)ˣ) (w : InfinitePlace F) :
    ((archIdele β : 𝔸ˣ) : 𝔸).1 w = β w := rfl

theorem archIdele_inv_fst (β : ∀ w : InfinitePlace F, (w.Completion)ˣ) (w : InfinitePlace F) :
    (((archIdele β)⁻¹ : 𝔸ˣ) : 𝔸).1 w = ((β w)⁻¹ : (w.Completion)ˣ) := rfl

theorem archIdele_snd (β : ∀ w : InfinitePlace F, (w.Completion)ˣ) : ((archIdele β : 𝔸ˣ) : 𝔸).2 = 1 := rfl

theorem archIdele_inv_snd (β : ∀ w : InfinitePlace F, (w.Completion)ˣ) :
    (((archIdele β)⁻¹ : 𝔸ˣ) : 𝔸).2 = 1 := rfl

theorem archCentralUnit_inv (w₀ : InfinitePlace F) (a : (w₀.Completion)ˣ) :
    (archCentralUnit F w₀ a)⁻¹ = archCentralUnit F w₀ a⁻¹ :=
  Units.ext rfl

theorem exists_translates_cover {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd : d₁ < d₂) {d₁' d₂' : ℝ} (hd₁' : 0 < d₁') :
    ∃ (K : ℕ) (lam : Fin (K + 1) → ℝ), (∀ k, 0 < lam k) ∧
      ∀ v : ℝ, d₁' ≤ v → v ≤ d₂' → ∃ k, lam k * d₁ ≤ v ∧ v ≤ lam k * d₂ := by
  set ρ : ℝ := d₂ / d₁ with hρ
  have hρ1 : 1 < ρ := (one_lt_div hd₁).mpr hd
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (d₂' / d₁') hρ1
  refine ⟨K, fun k => d₁' * ρ ^ (k : ℕ) / d₁, fun k => by positivity, fun v hv1 hv2 => ?_⟩
  have hex : ∃ k : ℕ, v ≤ d₁' * ρ ^ (k + 1) := by
    refine ⟨K, ?_⟩
    have h1 : v ≤ d₁' * ρ ^ K := by
      have : d₂' / d₁' < ρ ^ K := hK
      rw [div_lt_iff₀ hd₁'] at this
      linarith
    have h2 : d₁' * ρ ^ K ≤ d₁' * ρ ^ (K + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ1.le (Nat.le_succ K)) hd₁'.le
    linarith
  classical
  set k₀ := Nat.find hex with hk₀
  have hk₀K : k₀ ≤ K := Nat.find_min' hex (by
    have h1 : v ≤ d₁' * ρ ^ K := by
      have : d₂' / d₁' < ρ ^ K := hK
      rw [div_lt_iff₀ hd₁'] at this
      linarith
    have h2 : d₁' * ρ ^ K ≤ d₁' * ρ ^ (K + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ1.le (Nat.le_succ K)) hd₁'.le
    linarith)
  refine ⟨⟨k₀, Nat.lt_succ_of_le hk₀K⟩, ?_, ?_⟩
  ·
    show d₁' * ρ ^ k₀ / d₁ * d₁ ≤ v
    rw [div_mul_cancel₀ _ hd₁.ne']
    by_cases h0 : k₀ = 0
    · rw [h0, pow_zero, mul_one]; exact hv1
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero h0
      have hmin := Nat.find_min hex (show j < k₀ from by omega)
      rw [not_le] at hmin
      rw [hj]
      exact hmin.le
  ·
    show v ≤ d₁' * ρ ^ k₀ / d₁ * d₂
    have hspec : v ≤ d₁' * ρ ^ (k₀ + 1) := Nat.find_spec hex
    have : d₁' * ρ ^ k₀ / d₁ * d₂ = d₁' * ρ ^ (k₀ + 1) := by
      rw [pow_succ, hρ]; field_simp
    rw [this]; exact hspec

theorem exists_finset_arch_cover (c u : ℝ) {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    {d₁' d₂' : ℝ} (hd₁' : 0 < d₁') :
    ∃ A : Finset 𝔸ˣ, ∀ g ∈ centreCutSiegelSet F c u d₁' d₂',
      ∃ a ∈ A, ∃ s ∈ centreCutSiegelSet F c u d₁ d₂, g = s * centralScalar (𝓞 F) F a := by
  classical
  obtain ⟨K, lam, hlam, hcov⟩ := exists_translates_cover hd₁ hd (d₁' := d₁') (d₂' := d₂') hd₁'

  let b : ∀ w : InfinitePlace F, Fin (K + 1) → (w.Completion)ˣ := fun w k =>
    realUnit w (Real.sqrt (lam k)) (Real.sqrt_pos.mpr (hlam k)).ne'
  have hb : ∀ w k, ‖((b w k : (w.Completion)ˣ) : w.Completion)‖ ^ 2 = lam k := by
    intro w k
    show ‖realEmb w (Real.sqrt (lam k))‖ ^ 2 = lam k
    rw [norm_realEmb, sq_abs, Real.sq_sqrt (hlam k).le]
  let aOf : (InfinitePlace F → Fin (K + 1)) → 𝔸ˣ := fun k => archIdele fun w => b w (k w)
  refine ⟨(Finset.univ : Finset (InfinitePlace F → Fin (K + 1))).image aOf, fun g hg => ?_⟩
  obtain ⟨hK, hh, hx, hdet⟩ := mem_centreCutSiegelSet_iff.mp hg

  have hk : ∀ w, ∃ k, lam k * d₁ ≤ archDetNorm w g ∧ archDetNorm w g ≤ lam k * d₂ :=
    fun w => hcov _ (hdet w).1 (hdet w).2
  choose k hk1 hk2 using hk
  set a : 𝔸ˣ := aOf k with hadef
  refine ⟨a, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩,
    centralScalar (𝓞 F) F a⁻¹ * g, ?_, ?_⟩
  · refine mem_centreCutSiegelSet_iff.mpr ⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩
    · rw [map_mul]
      refine Subgroup.mul_mem _ (glFin_centralScalar_mem ?_ ?_) hK
      · intro v; exact one_mem _
      · intro v; exact one_mem _
    · rw [localHeight_centralScalar_mul]; exact hh w
    · rw [xWindowSq_centralScalar_mul]; exact hx w
    · rw [archDetNorm_centralScalar_mul', hadef]
      show ‖(((archIdele fun w => b w (k w))⁻¹ : 𝔸ˣ) : 𝔸).1 w‖ ^ 2 * archDetNorm w g ∈ Set.Icc d₁ d₂
      rw [archIdele_inv_fst, Units.val_inv_eq_inv_val, norm_inv, inv_pow, hb]
      have hl := hlam (k w)
      constructor
      · rw [le_inv_mul_iff₀ hl]; exact hk1 w
      · rw [inv_mul_le_iff₀ hl]; exact hk2 w
  · rw [map_inv, mul_assoc, mul_centralScalar_comm a g, inv_mul_cancel_left]

theorem exists_finset_cover_normOne {δ : ℝ} (hδ : 1 < δ) :
    ∃ J : Finset 𝔸ˣ, ∀ t ∈ normOneIdeles F, ∃ z ∈ J, ∃ r ∈ Rδ δ, ∃ a : Fˣ,
      t = z * r * Units.map (algebraMap F 𝔸).toMonoidHom a := by
  classical
  haveI := NumberField.TateGlobal.compactSpace_normOneIdeleClass F
  set H := normOneIdeles F with hH
  set P := (M4aHerbrand.principalIdeles (𝓞 F) F).subgroupOf H with hP
  set V : Set H := Subtype.val ⁻¹' Rδ δ with hV
  have hVopen : IsOpen V := (isOpen_Rδ δ).preimage continuous_subtype_val
  let U : H → Set (H ⧸ P) := fun z => QuotientGroup.mk '' ((fun v : H => z * v) '' V)
  have hUopen : ∀ z, IsOpen (U z) := fun z =>
    QuotientGroup.isOpenMap_coe _ (isOpenMap_mul_left z _ hVopen)
  have hUcov : (Set.univ : Set (H ⧸ P)) ⊆ ⋃ z, U z := by
    intro q _
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    refine Set.mem_iUnion.mpr ⟨t, ⟨t * 1, ⟨1, ?_, rfl⟩, by rw [mul_one]⟩⟩
    show ((1 : H) : 𝔸ˣ) ∈ Rδ δ
    exact one_mem_Rδ hδ
  obtain ⟨ι, hι⟩ := isCompact_univ.elim_finite_subcover U hUopen hUcov
  refine ⟨ι.image Subtype.val, fun t ht => ?_⟩
  have hq := hι (Set.mem_univ (QuotientGroup.mk (⟨t, ht⟩ : H) : H ⧸ P))
  simp only [Set.mem_iUnion] at hq
  obtain ⟨z, hz, hmem⟩ := hq
  obtain ⟨y, ⟨v, hv, rfl⟩, hyt⟩ := hmem

  have hrel : (z * v)⁻¹ * (⟨t, ht⟩ : H) ∈ P := QuotientGroup.eq.mp hyt
  rw [hP, Subgroup.mem_subgroupOf] at hrel
  obtain ⟨a, ha⟩ := hrel
  refine ⟨(z : 𝔸ˣ), Finset.mem_image.mpr ⟨z, hz, rfl⟩, (v : 𝔸ˣ), hv, a, ?_⟩
  have : (((z * v)⁻¹ * (⟨t, ht⟩ : H) : H) : 𝔸ˣ) = ((z : 𝔸ˣ) * (v : 𝔸ˣ))⁻¹ * t := rfl
  rw [this] at ha
  calc t = ((z : 𝔸ˣ) * (v : 𝔸ˣ)) * (((z : 𝔸ˣ) * (v : 𝔸ˣ))⁻¹ * t) := (mul_inv_cancel_left _ _).symm
    _ = _ := by rw [← ha]; rfl

theorem rpow_le_of_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {e : ℝ} (he : 0 ≤ e) : x ^ e ≤ y ^ e :=
  Real.rpow_le_rpow hx hxy he

end K1aSlabCover

end

open K1aSlabCover in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ ≤ e₂) :
    ∃ Z : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
        ∃ γ : Matrix.GeneralLinearGroup (Fin 2) F, ∃ z ∈ Z,
          globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z ∈
            ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ := by
  classical
  set 𝔖 : Set (AdelicGL2 (𝓞 F) F) := centreCutSiegelSet F c u d₁ d₂ with h𝔖def
  set D : Set (AdelicGL2 (𝓞 F) F) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ with hDdef

  have hTne : T.Nonempty := by
    obtain ⟨γ, z, hγ⟩ := hcov 1
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.mp hγ
    exact ⟨x, hx⟩

  set deg : ℕ := ∑ w : InfinitePlace F, w.mult with hdegdef
  set NT : AdelicGL2 (𝓞 F) F → ℝ := fun g => ideleNorm F (Matrix.GeneralLinearGroup.det g) with hNTdef
  set m₁ : ℝ := T.inf' hTne NT with hm₁def
  set m₂ : ℝ := T.sup' hTne NT with hm₂def
  have hm₁ : 0 < m₁ := (Finset.lt_inf'_iff hTne).2 fun x _ => ideleNorm_pos _

  set α2 : ℝ := d₁ ^ deg * m₁ / e₂ with hα2
  set β2 : ℝ := d₂ ^ deg * m₂ / e₁ with hβ2
  have he₂ : 0 < e₂ := lt_of_lt_of_le he₁ he
  have hα2pos : 0 < α2 := by positivity

  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  set m : ℕ := w₀.mult with hmdef
  have hm0 : m ≠ 0 := by rw [hmdef]; unfold InfinitePlace.mult; split_ifs <;> norm_num

  set Λ : ℝ := max 1 (max (Real.sqrt β2 ^ ((m : ℝ)⁻¹)) ((Real.sqrt α2 ^ ((m : ℝ)⁻¹))⁻¹)) with hΛ
  have hΛ1 : 1 ≤ Λ := le_max_left _ _
  have hΛpos : 0 < Λ := lt_of_lt_of_le one_pos hΛ1

  obtain ⟨J, hJ⟩ := exists_finset_cover_normOne (F := F) (δ := 2) one_lt_two

  set δ' : ℝ := 2 * Λ with hδ'
  have hδ'pos : 0 < δ' := by positivity
  obtain ⟨A, hA⟩ := exists_finset_arch_cover (F := F) c u hd₁ hd (d₁' := d₁ / δ' ^ 2) (d₂' := d₂ * δ' ^ 2)
    (by positivity)
  refine ⟨(J ×ˢ A).image (fun za => za.1 * za.2⁻¹), fun g hg => ?_⟩

  obtain ⟨γ, t, hmem⟩ := hcov g
  obtain ⟨x, hxT, s, hs, hsx⟩ : ∃ x ∈ T, ∃ s ∈ 𝔖, s * x = globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F t := by
    have := Set.mem_iUnion₂.mp hmem
    obtain ⟨x, hx, s, hs, hsx⟩ := this
    exact ⟨x, hx, s, hs, hsx⟩

  set n : ℝ := ideleNorm F t with hndef
  have hn : 0 < n := ideleNorm_pos _
  have hn2 : α2 ≤ n ^ 2 ∧ n ^ 2 ≤ β2 := by
    have hnorm : NT (s * x) = NT (globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F t) := by rw [hsx]
    simp only [hNTdef] at hnorm
    rw [ideleNorm_det_mul, mul_assoc, ideleNorm_det_globalPoints_mul, ideleNorm_det_mul,
      det_centralScalar, sq, ideleNorm_mul] at hnorm

    have hs' := ideleNorm_det_siegel (F := F) hd₁ hs
    have hx1 : m₁ ≤ ideleNorm F (Matrix.GeneralLinearGroup.det x) := Finset.inf'_le NT hxT
    have hx2 : ideleNorm F (Matrix.GeneralLinearGroup.det x) ≤ m₂ := Finset.le_sup' NT hxT
    have hg1 := hg.1
    have hg2 := hg.2
    have hgpos : 0 < ideleNorm F (Matrix.GeneralLinearGroup.det g) := ideleNorm_pos _
    have hprod_lo : d₁ ^ deg * m₁ ≤ ideleNorm F (Matrix.GeneralLinearGroup.det g) * (n * n) := by
      rw [← hnorm]
      exact mul_le_mul hs'.1 hx1 hm₁.le (le_trans (pow_nonneg hd₁.le _) hs'.1)
    have hprod_hi : ideleNorm F (Matrix.GeneralLinearGroup.det g) * (n * n) ≤ d₂ ^ deg * m₂ := by
      rw [← hnorm]
      exact mul_le_mul hs'.2 hx2 (ideleNorm_pos _).le (pow_nonneg (hd₁.le.trans hd.le) _)
    constructor
    · rw [hα2, div_le_iff₀ he₂, sq]
      calc d₁ ^ deg * m₁ ≤ ideleNorm F (Matrix.GeneralLinearGroup.det g) * (n * n) := hprod_lo
        _ ≤ e₂ * (n * n) := mul_le_mul_of_nonneg_right hg2 (by positivity)
        _ = n * n * e₂ := by ring
    · rw [hβ2, le_div_iff₀ he₁, sq]
      calc n * n * e₁ ≤ n * n * ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
            mul_le_mul_of_nonneg_left hg1 (by positivity)
        _ = ideleNorm F (Matrix.GeneralLinearGroup.det g) * (n * n) := by ring
        _ ≤ d₂ ^ deg * m₂ := hprod_hi
  have hnlo : Real.sqrt α2 ≤ n := by
    rw [← Real.sqrt_sq hn.le]; exact Real.sqrt_le_sqrt hn2.1
  have hnhi : n ≤ Real.sqrt β2 := by
    rw [← Real.sqrt_sq hn.le]; exact Real.sqrt_le_sqrt hn2.2

  have hρ : 0 < n ^ ((m : ℝ)⁻¹) := Real.rpow_pos_of_pos hn _
  set sN : (AdeleRing (𝓞 F) F)ˣ := sec w₀ (n ^ ((m : ℝ)⁻¹)) hρ with hsNdef
  have hsN : ideleNorm F sN = n := by
    rw [hsNdef, ideleNorm_sec]; exact Real.rpow_inv_natCast_pow hn.le hm0
  have hle1 : n ^ ((m : ℝ)⁻¹) ≤ Λ := by
    calc n ^ ((m : ℝ)⁻¹) ≤ Real.sqrt β2 ^ ((m : ℝ)⁻¹) := rpow_le_of_le hn.le hnhi (by positivity)
      _ ≤ Λ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hle2 : (n ^ ((m : ℝ)⁻¹))⁻¹ ≤ Λ := by
    have hαρ : 0 < Real.sqrt α2 ^ ((m : ℝ)⁻¹) := Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hα2pos) _
    calc (n ^ ((m : ℝ)⁻¹))⁻¹ ≤ (Real.sqrt α2 ^ ((m : ℝ)⁻¹))⁻¹ := by
          rw [inv_le_inv₀ hρ hαρ]
          exact rpow_le_of_le (Real.sqrt_nonneg _) hnlo (by positivity)
      _ ≤ Λ := le_trans (le_max_right _ _) (le_max_right _ _)

  have ht1 : t * sN⁻¹ ∈ normOneIdeles F := by
    rw [mem_normOneIdeles_iff, ideleNorm_mul, ideleNorm_inv, hsN, ← hndef, mul_inv_cancel₀ hn.ne']
  obtain ⟨z, hzJ, r, hr, a₀, hzr⟩ := hJ _ ht1

  set p : (AdeleRing (𝓞 F) F)ˣ := Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a₀ with hpdef
  have ht : t = z * (r * sN) * p := by
    have : t = (t * sN⁻¹) * sN := by rw [inv_mul_cancel_right]
    rw [this, hzr]
    simp only [mul_assoc, mul_comm, mul_left_comm]

  have hcomp : ∀ w : InfinitePlace F, ‖((sN : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ ≤ Λ ∧
      ‖((sN⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ ≤ Λ := by
    intro w
    rw [hsNdef]
    unfold sec
    rw [archCentralUnit_inv]
    by_cases hw : w = w₀
    · subst hw
      rw [archCentralUnit_fst_self, archCentralUnit_fst_self]
      unfold realUnit
      rw [Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv, norm_realEmb, abs_of_pos hρ]
      exact ⟨hle1, hle2⟩
    · rw [archCentralUnit_fst_of_ne _ _ hw, archCentralUnit_fst_of_ne _ _ hw, norm_one]
      exact ⟨hΛ1, hΛ1⟩
  have hrs : r * sN ∈ Rδ δ' := by
    have hfin1 : ((r * sN : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 =
        ((r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 := by
      rw [Units.val_mul, snd_mul, hsNdef]; unfold sec; rw [archCentralUnit_snd, mul_one]
    have hfin2 : (((r * sN)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 =
        ((r⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 := by
      rw [mul_inv_rev, Units.val_mul, snd_mul, hsNdef]; unfold sec
      rw [archCentralUnit_inv, archCentralUnit_snd, one_mul]
    have harch : ∀ (y q : AdeleRing (𝓞 F) F) (w : InfinitePlace F), ‖y.1 w‖ < 2 → ‖q.1 w‖ ≤ Λ →
        ‖(y * q).1 w‖ < δ' := by
      intro y q w hy hq
      rw [fst_mul_apply, norm_mul, hδ']
      calc ‖y.1 w‖ * ‖q.1 w‖ ≤ ‖y.1 w‖ * Λ := mul_le_mul_of_nonneg_left hq (norm_nonneg _)
        _ < 2 * Λ := mul_lt_mul_of_pos_right hy hΛpos
    refine ⟨⟨?_, fun w => ?_⟩, ⟨?_, fun w => ?_⟩⟩
    · rw [hfin1]; exact hr.1.1
    · rw [Units.val_mul]; exact harch _ _ w (hr.1.2 w) (hcomp w).1
    · rw [hfin2]; exact hr.2.1
    · rw [mul_inv_rev, Units.val_mul, fst_mul_apply, mul_comm, ← fst_mul_apply]
      exact harch _ _ w (hr.2.2 w) (hcomp w).2

  have hs1 : centralScalar (𝓞 F) F (r * sN)⁻¹ * s ∈ centreCutSiegelSet F c u (d₁ / δ' ^ 2) (d₂ * δ' ^ 2) :=
    centralScalar_mul_mem_siegel hδ'pos (inv_mem_Rδ hrs) hd₁.le hs
  obtain ⟨a, haA, s', hs', hss'⟩ := hA _ hs1

  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) a₀ * γ, z * a⁻¹,
    Finset.mem_image.mpr ⟨(z, a), Finset.mem_product.mpr ⟨hzJ, haA⟩, rfl⟩, ?_⟩

  have hcomm : ∀ (y : AdelicGL2 (𝓞 F) F) (w : (AdeleRing (𝓞 F) F)ˣ),
      y * centralScalar (𝓞 F) F w = centralScalar (𝓞 F) F w * y :=
    fun y w => mul_centralScalar_comm w y
  have hιg : globalPoints (𝓞 F) F γ * g = s * x * centralScalar (𝓞 F) F t⁻¹ := by
    rw [map_inv, eq_mul_inv_iff_mul_eq, hsx]
  have htinv : t⁻¹ = p⁻¹ * ((r * sN)⁻¹ * z⁻¹) := by rw [ht, mul_inv_rev, mul_inv_rev]
  have hgrp : t⁻¹ * p * (z * a⁻¹) = (r * sN)⁻¹ * a⁻¹ := by
    rw [htinv]
    calc p⁻¹ * ((r * sN)⁻¹ * z⁻¹) * p * (z * a⁻¹) = ((r * sN)⁻¹ * z⁻¹) * p⁻¹ * p * (z * a⁻¹) := by
          rw [mul_comm p⁻¹]
      _ = ((r * sN)⁻¹ * z⁻¹) * (z * a⁻¹) := by rw [inv_mul_cancel_right]
      _ = (r * sN)⁻¹ * a⁻¹ := by rw [mul_assoc, inv_mul_cancel_left]
  have step1 : globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a₀ * γ) * g *
      centralScalar (𝓞 F) F (z * a⁻¹) =
      s * x * (centralScalar (𝓞 F) F t⁻¹ * centralScalar (𝓞 F) F p * centralScalar (𝓞 F) F (z * a⁻¹)) := by
    rw [map_mul, globalPoints_scalar, ← hpdef, mul_assoc (centralScalar (𝓞 F) F p) (globalPoints (𝓞 F) F γ) g,
      hιg, ← hcomm (s * x * centralScalar (𝓞 F) F t⁻¹) p]
    simp only [mul_assoc]
  have step2 : centralScalar (𝓞 F) F t⁻¹ * centralScalar (𝓞 F) F p * centralScalar (𝓞 F) F (z * a⁻¹) =
      centralScalar (𝓞 F) F ((r * sN)⁻¹ * a⁻¹) := by
    rw [← map_mul, ← map_mul, hgrp]
  have step3 : s * x * centralScalar (𝓞 F) F ((r * sN)⁻¹ * a⁻¹) = s' * x := by
    rw [mul_assoc s x, hcomm x, ← mul_assoc s, map_mul, ← mul_assoc s, hcomm s (r * sN)⁻¹, hss',
      mul_assoc s', ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [step1, step2, step3]
  exact Set.mem_iUnion₂.mpr ⟨x, hxT, s', hs', rfl⟩

end S_AutomorphicForm_exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc (solution)
