-- Prove2me | solution 1 for AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/42011769-4472-55b7-a1ee-c0cc0b27ae73

import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_SiegelVolume
import Theorems.Thm_NumberField_Units_exists_forall_abs_sub_mult_mul_log_le
import Theorems.Thm_NumberField_mixedEmbedding_exists_forall_norm_embedding_sub_le
import Theorems.Thm_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le

open NumberField NumberField.InfinitePlace IsDedekindDomain Matrix Set

noncomputable section

namespace M4aP1R
namespace LowCover

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction AutomorphicForm.SiegelCovering NumberField.AdelicLevel NumberField.AdelicVolume NumberField.SiegelVolume

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
theorem exists_norm_eq (w : InfinitePlace F) {r : ℝ} (hr : 0 ≤ r) :
    ∃ a : w.Completion, ‖a‖ = r := by
  by_cases hw : IsReal w
  · refine ⟨(Completion.ringEquivRealOfIsReal hw).symm r, ?_⟩
    rw [← norm_extensionEmbeddingOfIsReal hw, ← Completion.ringEquivRealOfIsReal_apply hw,
      RingEquiv.apply_symm_apply, Real.norm_eq_abs, abs_of_nonneg hr]
  · have hc : IsComplex w := not_isReal_iff_isComplex.mp hw
    refine ⟨(Completion.ringEquivComplexOfIsComplex hc).symm r, ?_⟩
    rw [← norm_extensionEmbedding w, ← Completion.ringEquivComplexOfIsComplex_apply hc,
      RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

def archIdele (a : ∀ w : InfinitePlace F, (w.Completion)ˣ) : (AdeleRing (𝓞 F) F)ˣ where
  val := (fun w => (a w : w.Completion), 1)
  inv := (fun w => ((a w)⁻¹ : (w.Completion)ˣ), 1)
  val_inv := by
    refine Prod.ext (funext fun w => ?_) (one_mul 1)
    exact (a w).mul_inv
  inv_val := by
    refine Prod.ext (funext fun w => ?_) (one_mul 1)
    exact (a w).inv_mul

variable {F}

theorem glFin_centralScalar_archIdele (a : ∀ w : InfinitePlace F, (w.Completion)ˣ) :
    glFin (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_apply, Units.val_one]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, Matrix.one_apply_eq]
    rfl
  · rw [centralScalar_apply_ne _ h, Matrix.one_apply_ne h]
    rfl

theorem archComponent_centralScalar_archIdele_apply (a : ∀ w : InfinitePlace F, (w.Completion)ˣ)
    (w : InfinitePlace F) (i j : Fin 2) :
    ((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a))) :
        GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = if i = j then (a w : w.Completion) else 0 := by
  simp only [archComponent_apply, glArch_apply]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, if_pos rfl]
    rfl
  · rw [centralScalar_apply_ne _ h, if_neg h]
    rfl

section UpperGL

variable {L : Type*} [Field L]

def upperGL (e b : L) (he : e ≠ 0) : GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![e, b; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [he])

@[scoped simp] theorem upperGL_apply_zero_zero (e b : L) (he : e ≠ 0) :
    (upperGL e b he : Matrix (Fin 2) (Fin 2) L) 0 0 = e := rfl
@[scoped simp] theorem upperGL_apply_zero_one (e b : L) (he : e ≠ 0) :
    (upperGL e b he : Matrix (Fin 2) (Fin 2) L) 0 1 = b := rfl
@[scoped simp] theorem upperGL_apply_one_zero (e b : L) (he : e ≠ 0) :
    (upperGL e b he : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := rfl
@[scoped simp] theorem upperGL_apply_one_one (e b : L) (he : e ≠ 0) :
    (upperGL e b he : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := rfl

end UpperGL

theorem algebraMap_coe_mem_integralFiniteAdeles (b : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F) ∈ integralFiniteAdeles (𝓞 F) F := by
  intro v
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one b

theorem glFin_globalPoints_upperUnit_mem (ε : (𝓞 F)ˣ) (β : 𝓞 F)
    (hε : (((ε : 𝓞 F) : F)) ≠ 0) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F (upperGL ((ε : 𝓞 F) : F) (β : F) hε))
      ∈ finiteIntegralGL2 (𝓞 F) F := by
  set γ : GL (Fin 2) F := upperGL ((ε : 𝓞 F) : F) (β : F) hε with hγ

  have hε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.mpr (ε⁻¹).ne_zero
  have hεε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((ε : 𝓞 F) : F) = 1 := by
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, ← map_mul,
      show ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (ε : 𝓞 F) = 1 from ε.inv_mul, map_one]
  have hε'ε : ((ε : 𝓞 F) : F) * (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    rw [mul_comm]; exact hεε'
  set γ' : GL (Fin 2) F := upperGL (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)
    (-((((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * β : 𝓞 F) : F)) hε' with hγ'
  have hinv : γ⁻¹ = γ' := by
    refine inv_eq_of_mul_eq_one_right ?_
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Units.val_one]
    have hb : ((((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * β : 𝓞 F) : F)
        = (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * (β : F) := by
      rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap,
        RingOfIntegers.coe_eq_algebraMap, map_mul]
    fin_cases i <;> fin_cases j <;> simp [hγ, hγ', hb]
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j
    rw [glFin_globalPoints_apply]
    fin_cases i <;> fin_cases j
    · exact algebraMap_coe_mem_integralFiniteAdeles (ε : 𝓞 F)
    · exact algebraMap_coe_mem_integralFiniteAdeles β
    · simpa [hγ] using algebraMap_coe_mem_integralFiniteAdeles (F := F) 0
    · simpa [hγ] using algebraMap_coe_mem_integralFiniteAdeles (F := F) 1
  · intro i j
    rw [← map_inv, ← map_inv, hinv, glFin_globalPoints_apply]
    fin_cases i <;> fin_cases j
    · exact algebraMap_coe_mem_integralFiniteAdeles ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
    · simpa [hγ'] using
        algebraMap_coe_mem_integralFiniteAdeles (F := F) (-(((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * β))
    · simpa [hγ'] using algebraMap_coe_mem_integralFiniteAdeles (F := F) 0
    · simpa [hγ'] using algebraMap_coe_mem_integralFiniteAdeles (F := F) 1

theorem xAt_im_of_isReal {w : InfinitePlace F} (hw : IsReal w) (g : AdelicGL2 (𝓞 F) F) :
    (xAt w g).im = 0 := by
  set X : Matrix (Fin 2) (Fin 2) w.Completion :=
    ((archComponent F w (glArch (𝓞 F) F g) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) with hX
  have hM : ∀ i j, (X.map (Completion.extensionEmbedding w)) i j
      = ((Completion.extensionEmbeddingOfIsReal hw (X i j) : ℝ) : ℂ) := by
    intro i j
    rw [Matrix.map_apply, Completion.extensionEmbeddingOfIsReal_apply]
  unfold xAt xCoord
  rw [← hX, hM 0 0, hM 1 0, hM 0 1, hM 1 1, Complex.conj_ofReal, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_div]
  exact Complex.ofReal_im _

omit [NumberField F] in
theorem extensionEmbedding_coe_eq (w : InfinitePlace F) (x : F) :
    Completion.extensionEmbedding w (x : w.Completion) = w.embedding x := by
  exact Completion.extensionEmbedding_coe (v := w) (WithAbs.toAbs w.1 x)

omit [NumberField F] in
theorem embedding_im_of_isReal {w : InfinitePlace F} (hw : IsReal w) (x : F) :
    (w.embedding x).im = 0 := by
  rw [← embedding_of_isReal_apply hw]
  exact Complex.ofReal_im _

theorem place_laws (a : ∀ w : InfinitePlace F, (w.Completion)ˣ) {ε β : F} (hε : ε ≠ 0)
    (x : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F) :
    let y := centralScalar (𝓞 F) F (archIdele F a) *
      (globalPoints (𝓞 F) F (upperGL ε β hε) * x)
    localHeight (archComponent F w (glArch (𝓞 F) F y))
        = w ε * localHeight (archComponent F w (glArch (𝓞 F) F x)) ∧
      xAt w y = w.embedding ε * xAt w x + w.embedding β ∧
      archDetNorm w y = ‖(a w : w.Completion)‖ ^ 2 * (w ε * archDetNorm w x) := by
  intro y
  set S := archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a))) with hS
  set G := archComponent F w (glArch (𝓞 F) F
    (globalPoints (𝓞 F) F (upperGL ε β hε))) with hG
  set X := archComponent F w (glArch (𝓞 F) F x) with hX
  have hy : archComponent F w (glArch (𝓞 F) F y) = S * (G * X) := by
    simp only [y, map_mul, hS, hG, hX]
  have ha0 : (a w : w.Completion) ≠ 0 := (a w).ne_zero
  have hS00 : (S : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = (a w : w.Completion) := by
    rw [hS, archComponent_centralScalar_archIdele_apply, if_pos rfl]
  have hS01 : (S : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = 0 := by
    rw [hS, archComponent_centralScalar_archIdele_apply, if_neg (by decide)]
  have hS10 : (S : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
    rw [hS, archComponent_centralScalar_archIdele_apply, if_neg (by decide)]
  have hS11 : (S : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = (a w : w.Completion) := by
    rw [hS, archComponent_centralScalar_archIdele_apply, if_pos rfl]
  have hG00 : (G : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = (ε : w.Completion) := by
    rw [hG, archComponent_globalPoints_apply, upperGL_apply_zero_zero]
  have hG01 : (G : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = (β : w.Completion) := by
    rw [hG, archComponent_globalPoints_apply, upperGL_apply_zero_one]
  have hG10 : (G : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
    rw [hG, archComponent_globalPoints_apply, upperGL_apply_one_zero]
    exact NumberField.InfinitePlace.Completion.ext (by simp)
  have hG11 : (G : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = 1 := by
    rw [hG, archComponent_globalPoints_apply, upperGL_apply_one_one]
    exact NumberField.InfinitePlace.Completion.ext (by simp)
  have hε0 : ((ε : F) : w.Completion) ≠ 0 := by
    rw [← norm_pos_iff, norm_coe_completion]; exact w.pos_iff.mpr hε
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [hy, localHeight_upper_entries_mul ha0 hS00 hS10 hS11,
      localHeight_upper_entries_mul one_ne_zero hG00 hG10 hG11, div_self (norm_ne_zero_iff.mpr ha0),
      one_mul, norm_one, div_one, norm_coe_completion]
  ·
    set φ := Completion.extensionEmbedding w with hφ
    have hmat : ((S * (G * X) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2)
        w.Completion).map φ = ((Matrix.GeneralLinearGroup.map φ S *
          (Matrix.GeneralLinearGroup.map φ G * Matrix.GeneralLinearGroup.map φ X) :
            GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
      simp only [Units.val_mul, coe_map, Matrix.map_mul]
    unfold xAt
    rw [hy, hmat]
    have e : ∀ (T : GL (Fin 2) w.Completion) (i j : Fin 2),
        ((Matrix.GeneralLinearGroup.map φ T : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j
          = φ ((T : Matrix (Fin 2) (Fin 2) w.Completion) i j) := by
      intro T i j; rw [coe_map, Matrix.map_apply]
    rw [xCoord_upper_entries_mul (s := Matrix.GeneralLinearGroup.map φ S)
        ((map_ne_zero φ).mpr ha0) (by rw [e, hS00]) (by rw [e, hS01, map_zero])
        (by rw [e, hS10, map_zero]) (by rw [e, hS11]),
      xCoord_upper_entries_mul (s := Matrix.GeneralLinearGroup.map φ G) (t := (1 : ℂ))
        one_ne_zero (by rw [e, hG00]) (by rw [e, hG01]) (by rw [e, hG10, map_zero])
        (by rw [e, hG11, map_one]),
      div_self ((map_ne_zero φ).mpr ha0), one_mul, zero_div, add_zero, div_one, div_one,
      ← hX, coe_map, hφ, extensionEmbedding_coe_eq, extensionEmbedding_coe_eq]
  ·
    unfold archDetNorm
    rw [hy, det_upper_entries_mul hS00 hS10 hS11, det_upper_entries_mul hG00 hG10 hG11, ← hX,
      norm_mul, norm_mul, norm_mul, norm_mul, norm_one, mul_one, norm_coe_completion]
    ring

open Real in

theorem lowRegion_cover (c u T' : ℝ) (hc : 0 < c) :
    ∃ K : Set (AdelicGL2 (𝓞 F) F), IsCompact K ∧
      ∀ x ∈ integralWindowedSiegelSet F c u, archHeight F (glArch (𝓞 F) F x) ≤ T' →
        ∃ γ : GL (Fin 2) F, ∃ z : (AdeleRing (𝓞 F) F)ˣ,
          (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
            globalPoints (𝓞 F) F γ * x * centralScalar (𝓞 F) F z ∈ K := by
  classical

  obtain ⟨R, hR⟩ := NumberField.Units.exists_forall_abs_sub_mult_mul_log_le F
  obtain ⟨U, hU⟩ := NumberField.mixedEmbedding.exists_forall_norm_embedding_sub_le F
  set n : ℝ := (Module.finrank ℚ F : ℝ) with hn
  have hnpos : 0 < n := by
    rw [hn]; exact_mod_cast Module.finrank_pos
  by_cases hT : T' < c
  · refine ⟨∅, isCompact_empty, fun x hx hxT => ?_⟩
    exact absurd (lt_of_le_of_lt (hx.2.1.trans hxT) hT) (lt_irrefl _)
  push Not at hT
  have hT0 : 0 < T' := hc.trans_le hT
  set lo : ℝ := Real.log c / n - R with hlo
  set hi : ℝ := Real.log T' / n + R with hhi
  refine ⟨centreCutSiegelSet F (Real.exp lo) U 1 1 ∩
      {g | ∀ w : InfinitePlace F,
        localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ Real.exp hi},
    AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap F
      (Real.exp_pos lo) one_pos, fun x hx hxT => ?_⟩
  obtain ⟨hfin, hHc, hwin⟩ := hx

  have hH0 : 0 < archHeight F (glArch (𝓞 F) F x) := hc.trans_le hHc
  have hh0 : ∀ w : InfinitePlace F, 0 < localHeight (archComponent F w (glArch (𝓞 F) F x)) :=
    fun w => localHeight_pos _
  have hlogH : Real.log (archHeight F (glArch (𝓞 F) F x))
      = ∑ w : InfinitePlace F,
          (w.mult : ℝ) * Real.log (localHeight (archComponent F w (glArch (𝓞 F) F x))) := by
    unfold archHeight
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [Real.log_pow]
    · intro w _
      exact (pow_pos (hh0 w) _).ne'
  have hsum_mult : ∑ w : InfinitePlace F, (w.mult : ℝ) = n := by
    rw [hn, ← sum_mult_eq (K := F), Nat.cast_sum]

  set t : InfinitePlace F → ℝ := fun w =>
    (w.mult : ℝ) * (Real.log (archHeight F (glArch (𝓞 F) F x)) / n)
      - (w.mult : ℝ) * Real.log (localHeight (archComponent F w (glArch (𝓞 F) F x))) with htdef
  have ht : ∑ w, t w = 0 := by
    simp only [htdef]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum_mult, ← hlogH]
    have : n * (Real.log (archHeight F (glArch (𝓞 F) F x)) / n)
        = Real.log (archHeight F (glArch (𝓞 F) F x)) := by
      field_simp
    rw [this, sub_self]
  obtain ⟨ε, hε⟩ := hR t ht
  have he0 : (((ε : 𝓞 F) : F)) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ε.ne_zero
  have hwe : ∀ w : InfinitePlace F, 0 < w ((ε : 𝓞 F) : F) := fun w => w.pos_iff.mpr he0
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hε (Classical.arbitrary _))

  have hbal : ∀ w : InfinitePlace F,
      Real.exp lo ≤ w ((ε : 𝓞 F) : F) * localHeight (archComponent F w (glArch (𝓞 F) F x)) ∧
      w ((ε : 𝓞 F) : F) * localHeight (archComponent F w (glArch (𝓞 F) F x)) ≤ Real.exp hi := by
    intro w
    have hm1 : (1 : ℝ) ≤ w.mult := one_le_mult
    have hy0 : 0 < w ((ε : 𝓞 F) : F) * localHeight (archComponent F w (glArch (𝓞 F) F x)) :=
      mul_pos (hwe w) (hh0 w)
    have hεw := hε w
    have hkey : t w - (w.mult : ℝ) * Real.log (w ((ε : 𝓞 F) : F))
        = (w.mult : ℝ) * (Real.log (archHeight F (glArch (𝓞 F) F x)) / n
          - Real.log (w ((ε : 𝓞 F) : F) *
              localHeight (archComponent F w (glArch (𝓞 F) F x)))) := by
      simp only [htdef]
      rw [Real.log_mul (hwe w).ne' (hh0 w).ne']
      ring
    rw [hkey, abs_le] at hεw
    obtain ⟨hlow, hup⟩ := hεw
    set d := Real.log (archHeight F (glArch (𝓞 F) F x)) / n
      - Real.log (w ((ε : 𝓞 F) : F) * localHeight (archComponent F w (glArch (𝓞 F) F x))) with hd
    have h1 : d ≤ R := by
      by_cases hd0 : 0 ≤ d
      · nlinarith
      · linarith
    have h2 : -R ≤ d := by
      by_cases hd0 : d ≤ 0
      · nlinarith
      · linarith
    have hLc : Real.log c / n ≤ Real.log (archHeight F (glArch (𝓞 F) F x)) / n :=
      div_le_div_of_nonneg_right (Real.log_le_log hc hHc) hnpos.le
    have hLT : Real.log (archHeight F (glArch (𝓞 F) F x)) / n ≤ Real.log T' / n :=
      div_le_div_of_nonneg_right (Real.log_le_log hH0 hxT) hnpos.le
    constructor
    · rw [← Real.exp_log hy0]
      exact Real.exp_le_exp.mpr (by rw [hlo]; linarith)
    · rw [← Real.exp_log hy0]
      exact Real.exp_le_exp.mpr (by rw [hhi]; linarith)

  set ξ : InfinitePlace F → ℂ := fun w => -(w.embedding ((ε : 𝓞 F) : F) * xAt w x) with hξdef
  have hξ : ∀ w : InfinitePlace F, w.IsReal → (ξ w).im = 0 := by
    intro w hw
    simp only [hξdef, Complex.neg_im, Complex.mul_im, embedding_im_of_isReal hw,
      xAt_im_of_isReal hw, mul_zero, zero_mul, add_zero, neg_zero]
  obtain ⟨β, hβ⟩ := hU ξ hξ

  have hD0 : ∀ w : InfinitePlace F, 0 < w ((ε : 𝓞 F) : F) * archDetNorm w x :=
    fun w => mul_pos (hwe w) (archDetNorm_pos w x)
  have hr : ∀ w : InfinitePlace F, ∃ aw : (w.Completion)ˣ,
      ‖(aw : w.Completion)‖ ^ 2 * (w ((ε : 𝓞 F) : F) * archDetNorm w x) = 1 := by
    intro w
    have hsq : 0 < Real.sqrt (w ((ε : 𝓞 F) : F) * archDetNorm w x) := Real.sqrt_pos.mpr (hD0 w)
    obtain ⟨a0, ha0⟩ := exists_norm_eq F w
      (r := (Real.sqrt (w ((ε : 𝓞 F) : F) * archDetNorm w x))⁻¹) (by positivity)
    have ha0ne : a0 ≠ 0 := by
      rw [← norm_pos_iff, ha0]; positivity
    refine ⟨Units.mk0 a0 ha0ne, ?_⟩
    rw [Units.val_mk0, ha0, inv_pow, Real.sq_sqrt (hD0 w).le, inv_mul_cancel₀ (hD0 w).ne']
  choose a ha using hr

  refine ⟨upperGL ((ε : 𝓞 F) : F) (β : F) he0, archIdele F a, rfl, ?_⟩
  rw [mul_centralScalar_comm]
  have hlaw := fun w : InfinitePlace F =>
    place_laws (F := F) a (β := (β : F)) he0 x w
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    rw [map_mul, map_mul, glFin_centralScalar_archIdele, one_mul]
    exact (finiteIntegralGL2 (𝓞 F) F).mul_mem (glFin_globalPoints_upperUnit_mem ε β he0) hfin
  ·
    intro w
    rw [(hlaw w).1]
    exact (hbal w).1
  ·
    intro w
    rw [xWindowSq_eq_norm_xAt_sq, (hlaw w).2.1]
    have hb : ‖w.embedding ((ε : 𝓞 F) : F) * xAt w x + w.embedding (β : F)‖ ≤ U := by
      have : w.embedding (β : F) - ξ w
          = w.embedding ((ε : 𝓞 F) : F) * xAt w x + w.embedding (β : F) := by
        simp only [hξdef]; ring
      rw [← this]
      exact hβ w
    nlinarith [norm_nonneg (w.embedding ((ε : 𝓞 F) : F) * xAt w x + w.embedding (β : F)), hb]
  ·
    intro w
    rw [(hlaw w).2.2, ha w]
    exact ⟨le_rfl, le_rfl⟩
  ·
    intro w
    show localHeight _ ≤ Real.exp hi
    rw [(hlaw w).1]
    exact (hbal w).2

end M4aP1R.LowCover
p2m_reactivate "P2MW.S_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le.M4aP1R P2MW.S_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le.M4aP1R.LowCover"
p2m_reactivate "P2MW.S_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le.M4aP1R"

theorem M4aP1R.LowCover.exists_isCompact_cover_of_archHeight_le_impl
    (F : Type) [Field F] [NumberField F] (c u T' : ℝ) (hc : 0 < c) :
    ∃ K : Set (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F),
      IsCompact K ∧
        ∀ x ∈ AutomorphicForm.WindowedSiegel.integralWindowedSiegelSet F c u,
          AutomorphicForm.WindowedSiegel.archHeight F
              (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F x) ≤ T' →
            ∃ γ : Matrix.GeneralLinearGroup (Fin 2) F,
              ∃ z : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ,
                (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
                  AutomorphicForm.globalPoints (NumberField.RingOfIntegers F) F γ * x *
                      AutomorphicForm.centralScalar (NumberField.RingOfIntegers F) F z ∈ K :=
  M4aP1R.LowCover.lowRegion_cover (F := F) c u T' hc

theorem solution
    (F : Type) [Field F] [NumberField F] (c u T' : ℝ) (hc : 0 < c) :
    ∃ K : Set (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F),
      IsCompact K ∧
        ∀ x ∈ AutomorphicForm.WindowedSiegel.integralWindowedSiegelSet F c u,
          AutomorphicForm.WindowedSiegel.archHeight F
              (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F x) ≤ T' →
            ∃ γ : Matrix.GeneralLinearGroup (Fin 2) F,
              ∃ z : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ,
                (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
                  AutomorphicForm.globalPoints (NumberField.RingOfIntegers F) F γ * x *
                      AutomorphicForm.centralScalar (NumberField.RingOfIntegers F) F z ∈ K := by
  exact M4aP1R.LowCover.exists_isCompact_cover_of_archHeight_le_impl F c u T' hc

end
end S_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le
end P2MW
export P2MW.S_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le (solution)
