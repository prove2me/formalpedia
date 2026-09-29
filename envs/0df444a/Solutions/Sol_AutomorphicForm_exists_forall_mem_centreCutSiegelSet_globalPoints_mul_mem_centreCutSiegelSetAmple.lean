-- Prove2me | solution 1 for AutomorphicForm.exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/90e2bcf7-6167-50e8-bdd5-f1352147c773

import Mathlib
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_SiegelReduction
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_NumberField_Units_exists_forall_abs_two_mul_log_add_log_sub_div_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple

set_option autoImplicit false
set_option maxHeartbeats 1600000

open NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

noncomputable section

namespace Ws23
namespace Cover

open NumberField.InfinitePlace AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction
open NumberField.AdelicVolume NumberField.AdelicCentre

variable (F : Type) [Field F] [NumberField F]

theorem algebraMap_coe_mem_integralFiniteAdeles (r : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (r : F) ∈ integralFiniteAdeles (𝓞 F) F := by
  intro v
  rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one r

theorem glFin_globalPoints_mem_of_integral (γ : GL (Fin 2) F)
    (h : ∀ i j, ∃ r : 𝓞 F, (γ : Matrix (Fin 2) (Fin 2) F) i j = r)
    (h' : ∀ i j, ∃ r : 𝓞 F, ((γ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = r) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) ∈ finiteIntegralGL2 (𝓞 F) F := by
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j
    rw [glFin_globalPoints_apply]
    obtain ⟨r, hr⟩ := h i j
    rw [hr]
    exact algebraMap_coe_mem_integralFiniteAdeles F r
  · intro i j
    rw [← map_inv, ← map_inv, glFin_globalPoints_apply]
    obtain ⟨r, hr⟩ := h' i j
    rw [hr]
    exact algebraMap_coe_mem_integralFiniteAdeles F r

def unitF (ε : (𝓞 F)ˣ) : Fˣ := Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) ε

theorem unitF_val (ε : (𝓞 F)ˣ) : ((unitF F ε : Fˣ) : F) = ((ε : 𝓞 F) : F) := rfl

theorem glFin_globalPoints_diagOne_mem (ε : (𝓞 F)ˣ) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F (diagOne (unitF F ε))) ∈ finiteIntegralGL2 (𝓞 F) F := by
  refine glFin_globalPoints_mem_of_integral F _ (fun i j => ?_) (fun i j => ?_)
  · rw [diagOne_coe_apply]
    fin_cases i <;> fin_cases j
    · exact ⟨ε, rfl⟩
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · rw [← map_inv, diagOne_coe_apply]
    fin_cases i <;> fin_cases j
    · exact ⟨((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F), by simp [unitF]⟩
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem glFin_globalPoints_unipotentGL2_mem (β : 𝓞 F) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F (unipotentGL2 (β : F))) ∈ finiteIntegralGL2 (𝓞 F) F := by
  refine glFin_globalPoints_mem_of_integral F _ (fun i j => ?_) (fun i j => ?_)
  · rw [unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact ⟨1, by simp⟩
    · exact ⟨β, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · have hinv : ((unipotentGL2 (β : F))⁻¹ : GL (Fin 2) F) = unipotentGL2 (-(β : F)) := by
      rw [inv_eq_iff_mul_eq_one, ← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero]
    rw [hinv, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact ⟨1, by simp⟩
    · exact ⟨-β, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

def archIdele (a : ∀ w : InfinitePlace F, (w.Completion)ˣ) : (AdeleRing (𝓞 F) F)ˣ where
  val := (fun w => (a w : w.Completion), 1)
  inv := (fun w => ((a w)⁻¹ : (w.Completion)ˣ), 1)
  val_inv := Prod.ext (funext fun w => (a w).mul_inv) (one_mul 1)
  inv_val := Prod.ext (funext fun w => (a w).inv_mul) (one_mul 1)

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

theorem archComponent_centralScalar_archIdele (w : InfinitePlace F) (a : ∀ w : InfinitePlace F, (w.Completion)ˣ) :
    (((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a))) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = (a w : w.Completion)) ∧
    (((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a))) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = 0) ∧
    (((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a))) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0) ∧
    (((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archIdele F a))) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = (a w : w.Completion)) := by
  simp only [archComponent_apply, glArch_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [centralScalar_apply_eq]; rfl
  · rw [centralScalar_apply_ne _ (by decide)]; rfl
  · rw [centralScalar_apply_ne _ (by decide)]; rfl
  · rw [centralScalar_apply_eq]; rfl

open NumberField.InfinitePlace.Completion in
theorem norm_ringEquivRealOfIsReal' {w : InfinitePlace F} (hw : w.IsReal) (x : w.Completion) :
    ‖ringEquivRealOfIsReal hw x‖ = ‖x‖ :=
  (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) x

open NumberField.InfinitePlace.Completion in
theorem norm_ringEquivComplexOfIsComplex' {w : InfinitePlace F} (hw : w.IsComplex) (x : w.Completion) :
    ‖ringEquivComplexOfIsComplex hw x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

open NumberField.InfinitePlace.Completion in
open scoped Classical in

def ofRealAt (w : InfinitePlace F) : ℝ →+* w.Completion :=
  if hw : w.IsReal then (ringEquivRealOfIsReal hw).symm.toRingHom
  else ((ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm.toRingHom).comp Complex.ofRealHom

open NumberField.InfinitePlace.Completion in
theorem norm_ofRealAt (w : InfinitePlace F) (t : ℝ) : ‖ofRealAt F w t‖ = |t| := by
  classical
  unfold ofRealAt
  split_ifs with hw
  · have h := norm_ringEquivRealOfIsReal' F hw ((ringEquivRealOfIsReal hw).symm t)
    rw [RingEquiv.apply_symm_apply, Real.norm_eq_abs] at h
    show ‖(ringEquivRealOfIsReal hw).symm t‖ = |t|
    exact h.symm
  · have h := norm_ringEquivComplexOfIsComplex' F (not_isReal_iff_isComplex.mp hw)
      ((ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm (t : ℂ))
    rw [RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_eq_abs] at h
    show ‖(ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm (t : ℂ)‖ = |t|
    exact h.symm

theorem step_place (w : InfinitePlace F) (S U Z : GL (Fin 2) w.Completion) (a b z : w.Completion)
    (ha : a ≠ 0) (hz : z ≠ 0)
    (hU00 : (U : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = a) (hU01 : (U : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = b)
    (hU10 : (U : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0) (hU11 : (U : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = 1)
    (hZ00 : (Z : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = z) (hZ01 : (Z : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = 0)
    (hZ10 : (Z : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0) (hZ11 : (Z : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = z) :
    localHeight (Z * (U * S)) = ‖a‖ * localHeight S ∧
    ‖((Z * (U * S) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖ =
      ‖z‖ ^ 2 * ‖a‖ * ‖(S : Matrix (Fin 2) (Fin 2) w.Completion).det‖ ∧
    xWindowSq (Z * (U * S)) =
      ‖InfinitePlace.Completion.extensionEmbedding w a *
          xCoord (((S : Matrix (Fin 2) (Fin 2) w.Completion)).map (InfinitePlace.Completion.extensionEmbedding w)) +
        InfinitePlace.Completion.extensionEmbedding w b‖ ^ 2 := by
  set φ := InfinitePlace.Completion.extensionEmbedding w with hφ
  have hφn : ∀ x, ‖φ x‖ = ‖x‖ := norm_extensionEmbedding w
  refine ⟨?_, ?_, ?_⟩
  · rw [localHeight_scalar_entries_mul hz hZ00 hZ01 hZ10 hZ11, localHeight_upper_entries_mul one_ne_zero hU00 hU10 hU11,
      norm_one, div_one]
  · rw [det_upper_entries_mul hZ00 hZ10 hZ11, det_upper_entries_mul hU00 hU10 hU11, norm_mul, norm_mul, norm_mul,
      norm_mul, norm_one, mul_one, sq]
    ring
  · rw [xWindowSq_scalar_entries_mul hz hZ00 hZ01 hZ10 hZ11, xWindowSq_eq_norm_xCoord_map_sq φ hφn,
      ← coe_map φ (U * S), map_mul]
    have h := xCoord_upper_entries_mul (s := Matrix.GeneralLinearGroup.map φ U) (g := Matrix.GeneralLinearGroup.map φ S)
      (a := φ a) (b := φ b) (t := 1) one_ne_zero
      (by rw [coe_map, Matrix.map_apply, hU00]) (by rw [coe_map, Matrix.map_apply, hU01])
      (by rw [coe_map, Matrix.map_apply, hU10, map_zero]) (by rw [coe_map, Matrix.map_apply, hU11, map_one])
    rw [h, coe_map, div_one, div_one]

open NumberField.Units NumberField.Units.dirichletUnitTheorem in

theorem exists_unit_log_balance (K : Type) [Field K] [NumberField K] :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ t : InfinitePlace K → ℝ, ∃ ε : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
      |t w + Real.log (w ((ε : 𝓞 K) : K)) -
        (∑ w' : InfinitePlace K, (w'.mult : ℝ) * t w') / (∑ w' : InfinitePlace K, (w'.mult : ℝ))| ≤ ρ := by
  classical

  let b : Module.Basis (Fin (rank K)) ℝ (logSpace K) := (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded b).exists_norm_le
  set R' : ℝ := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hR'' : ∀ y ∈ ZSpan.fundamentalDomain b, ‖y‖ ≤ R' := fun y hy => (hR y hy).trans (le_max_left _ _)
  set N : ℝ := (Fintype.card (InfinitePlace K) : ℝ) with hN
  have hN1 : 1 ≤ N := by
    rw [hN]; exact_mod_cast Fintype.card_pos
  refine ⟨N * R', mul_nonneg (by linarith) hR'0, fun t => ?_⟩

  set M : ℝ := ∑ w' : InfinitePlace K, (w'.mult : ℝ) with hM
  have hM0 : 0 < M := by
    rw [hM]
    exact Finset.sum_pos (fun w _ => by exact_mod_cast (mult_pos (w := w))) Finset.univ_nonempty
  set s : ℝ := (∑ w' : InfinitePlace K, (w'.mult : ℝ) * t w') / M with hs
  set d : InfinitePlace K → ℝ := fun w => t w - s with hd
  have hdsum : ∑ w : InfinitePlace K, (w.mult : ℝ) * d w = 0 := by
    simp only [hd, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hs, ← hM, mul_div_cancel₀ _ hM0.ne', sub_self]

  set x : logSpace K := fun w => (w.1.mult : ℝ) * d w.1 with hx
  obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
  have hvL : (v : logSpace K) ∈ unitLattice K := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ (unitLattice K) (basisUnitLattice K)]
    exact v.2
  obtain ⟨y, -, hy⟩ := Submodule.mem_map.mp hvL
  set u : (𝓞 K)ˣ := Additive.toMul y with hu
  have hyu : logEmbedding K (Additive.ofMul u) = (v : logSpace K) := by rw [hu, ofMul_toMul]; exact hy
  have hnorm : ‖(v : logSpace K) + x‖ ≤ R' := hR'' _ hv

  have hoff : ∀ w : InfinitePlace K, w ≠ w₀ → |(w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K)) + (w.mult : ℝ) * d w| ≤ R' := by
    intro w hw
    have h := (norm_le_pi_norm ((v : logSpace K) + x) ⟨w, hw⟩).trans hnorm
    rw [Pi.add_apply, Real.norm_eq_abs, ← hyu, logEmbedding_component] at h
    exact h

  have hprod : ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K)) = 0 := sum_mult_mul_log u
  have hall : ∑ w : InfinitePlace K, ((w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K)) + (w.mult : ℝ) * d w) = 0 := by
    rw [Finset.sum_add_distrib, hprod, hdsum, add_zero]
  have hw₀ : |((w₀ : InfinitePlace K).mult : ℝ) * Real.log (w₀ ((u : 𝓞 K) : K)) + ((w₀ : InfinitePlace K).mult : ℝ) * d w₀|
      ≤ N * R' := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀, add_eq_zero_iff_eq_neg] at hall
    rw [hall, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : {w : InfinitePlace K // w ≠ w₀}, |(w.1.mult : ℝ) * Real.log (w.1 ((u : 𝓞 K) : K)) + (w.1.mult : ℝ) * d w.1|
        ≤ ∑ _w : {w : InfinitePlace K // w ≠ w₀}, R' := Finset.sum_le_sum fun w _ => hoff w.1 w.2
      _ ≤ N * R' := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hN]
          refine mul_le_mul_of_nonneg_right ?_ hR'0
          exact_mod_cast Fintype.card_subtype_le _

  have hcoord : ∀ w : InfinitePlace K, |Real.log (w ((u : 𝓞 K) : K)) + d w| ≤ N * R' := by
    intro w
    have hm1 : (1 : ℝ) ≤ w.mult := by exact_mod_cast (mult_pos (w := w))
    have hm0 : (0 : ℝ) < w.mult := lt_of_lt_of_le one_pos hm1
    have key : |(w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K)) + (w.mult : ℝ) * d w| ≤ N * R' := by
      by_cases hw : w = w₀
      · subst hw
        exact hw₀
      · exact (hoff w hw).trans (le_mul_of_one_le_left hR'0 hN1)
    rw [← mul_add, abs_mul, abs_of_pos hm0] at key
    calc |Real.log (w ((u : 𝓞 K) : K)) + d w| = 1 * |Real.log (w ((u : 𝓞 K) : K)) + d w| := (one_mul _).symm
      _ ≤ (w.mult : ℝ) * |Real.log (w ((u : 𝓞 K) : K)) + d w| := mul_le_mul_of_nonneg_right hm1 (abs_nonneg _)
      _ ≤ N * R' := key

  refine ⟨u, fun w => ?_⟩
  have h := hcoord w
  rw [hd] at h
  dsimp only at h
  rw [show t w + Real.log (w ((u : 𝓞 K) : K)) - s = Real.log (w ((u : 𝓞 K) : K)) + (t w - s) by ring]
  exact h

section L3
open NumberField.mixedEmbedding

open scoped Classical in

theorem exists_int_translate_le :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y : InfinitePlace F → ℂ, (∀ w : InfinitePlace F, w.IsReal → (y w).im = 0) →
      ∃ β : 𝓞 F, ∀ w : InfinitePlace F, ‖y w + (w.embedding : F →+* ℂ) (β : F)‖ ≤ R := by
  classical
  set b := mixedEmbedding.latticeBasis F with hb
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded b).exists_norm_le
  refine ⟨max R 0, le_max_right _ _, fun y hy => ?_⟩

  set x : mixedSpace F := (fun w => (y w.1).re, fun w => y w.1) with hx
  have hmem : ((ZSpan.floor b x : Submodule.span ℤ (Set.range b)) : mixedSpace F) ∈ mixedEmbedding.integerLattice F :=
    (mixedEmbedding.mem_span_latticeBasis F).mp (ZSpan.floor b x).2
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : 𝓞 F, mixedEmbedding F (β₀ : F) = (ZSpan.floor b x : mixedSpace F) := Set.mem_range.mp hmem
  have hfr : ‖x - mixedEmbedding F (β₀ : F)‖ ≤ R := by
    rw [hβ₀, ← ZSpan.fract_apply]
    exact hR _ (ZSpan.fract_mem_fundamentalDomain b x)
  refine ⟨-β₀, fun w => ?_⟩
  have hneg : (w.embedding : F →+* ℂ) (((-β₀ : 𝓞 F) : F)) = -(w.embedding (β₀ : F)) := by
    push_cast
    exact map_neg _ _
  rw [hneg, ← sub_eq_add_neg]
  refine le_trans ?_ (le_trans hfr (le_max_left _ _))
  by_cases hw : w.IsReal
  ·
    have h1 : ‖(x - mixedEmbedding F (β₀ : F)).1 ⟨w, hw⟩‖ ≤ ‖x - mixedEmbedding F (β₀ : F)‖ :=
      (norm_le_pi_norm _ _).trans (le_max_left _ _)
    refine le_trans (le_of_eq ?_) h1
    rw [Prod.fst_sub, Pi.sub_apply, mixedEmbedding_apply_isReal]
    have hyw : y w = ((y w).re : ℂ) := by
      apply Complex.ext <;> simp [hy w hw]
    have hemb : w.embedding (β₀ : F) = ((embedding_of_isReal hw (β₀ : F) : ℝ) : ℂ) :=
      (embedding_of_isReal_apply hw _).symm
    rw [hyw, hemb, ← Complex.ofReal_sub, Complex.norm_real]
  ·
    have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    have h1 : ‖(x - mixedEmbedding F (β₀ : F)).2 ⟨w, hw'⟩‖ ≤ ‖x - mixedEmbedding F (β₀ : F)‖ :=
      (norm_le_pi_norm _ _).trans (le_max_right _ _)
    refine le_trans (le_of_eq ?_) h1
    rw [Prod.snd_sub, Pi.sub_apply, mixedEmbedding_apply_isComplex]

end L3

open ComplexConjugate

theorem im_extensionEmbedding_of_isReal {w : InfinitePlace F} (hw : w.IsReal) (x : w.Completion) :
    (InfinitePlace.Completion.extensionEmbedding w x).im = 0 := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x, Complex.ofReal_im]

theorem im_xCoord_eq_zero (M : Matrix (Fin 2) (Fin 2) ℂ) (h : ∀ i j, (M i j).im = 0) : (xCoord M).im = 0 := by
  unfold xCoord
  rw [Complex.div_ofReal_im]
  have hnum : (M 0 0 * conj (M 1 0) + M 0 1 * conj (M 1 1)).im = 0 := by
    simp [Complex.add_im, Complex.mul_im, Complex.conj_im, Complex.conj_re, h]
  rw [hnum, zero_div]

theorem redElt_coe (ε : (𝓞 F)ˣ) (β : 𝓞 F) :
    ((unipotentGL2 ((β : F)) * diagOne (unitF F ε) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((ε : 𝓞 F) : F), (β : F); 0, 1] := by
  rw [Units.val_mul, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply, Matrix.diagonal, unitF_val]

section Delta

theorem unit_inv_coe (ε : (𝓞 F)ˣ) : ((((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) : F) = (((ε : 𝓞 F) : F))⁻¹ := by
  have h : (((ε : 𝓞 F) : F)) * ((((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) : F) = 1 := by
    rw [← map_mul (algebraMap (𝓞 F) F), show ((ε : 𝓞 F)) * ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) = 1 from by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one], map_one]
  have hε : (((ε : 𝓞 F) : F)) ≠ 0 := by exact_mod_cast ε.ne_zero
  exact (eq_inv_of_mul_eq_one_right h)

def delta (ε : (𝓞 F)ˣ) (β : 𝓞 F) : GL (Fin 2) F where
  val := !![((ε : 𝓞 F) : F), ((β : 𝓞 F) : F); 0, (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)]
  inv := !![(((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F), -((β : 𝓞 F) : F); 0, ((ε : 𝓞 F) : F)]
  val_inv := by
    have hε : (((ε : 𝓞 F) : F)) ≠ 0 := by exact_mod_cast ε.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, unit_inv_coe, hε] <;> ring
  inv_val := by
    have hε : (((ε : 𝓞 F) : F)) ≠ 0 := by exact_mod_cast ε.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, unit_inv_coe, hε] <;> ring

theorem delta_coe (ε : (𝓞 F)ˣ) (β : 𝓞 F) :
    ((delta F ε β : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((ε : 𝓞 F) : F), ((β : 𝓞 F) : F); 0, (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)] := rfl

theorem delta_inv_coe (ε : (𝓞 F)ˣ) (β : 𝓞 F) :
    (((delta F ε β)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F), -((β : 𝓞 F) : F); 0, ((ε : 𝓞 F) : F)] := rfl

theorem glFin_globalPoints_delta_mem (ε : (𝓞 F)ˣ) (β : 𝓞 F) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F (delta F ε β)) ∈ finiteIntegralGL2 (𝓞 F) F := by
  refine glFin_globalPoints_mem_of_integral F _ (fun i j => ?_) (fun i j => ?_)
  · rw [delta_coe]
    fin_cases i <;> fin_cases j
    · exact ⟨ε, rfl⟩
    · exact ⟨β, rfl⟩
    · exact ⟨0, by simp⟩
    · exact ⟨((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F), rfl⟩
  · rw [delta_inv_coe]
    fin_cases i <;> fin_cases j
    · exact ⟨((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F), rfl⟩
    · exact ⟨-β, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨ε, rfl⟩

end Delta

section Main

p2m_open "NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace"

theorem main :
    ∃ κ R θ : ℝ, 1 ≤ κ ∧ 0 < θ ∧
      ∀ (c u d₁ d₂ : ℝ), ∀ g ∈ centreCutSiegelSet F c u d₁ d₂,
        ∃ δ : GL (Fin 2) F,
          (∃ (ε : (𝓞 F)ˣ) (β : 𝓞 F),
              (δ : Matrix (Fin 2) (Fin 2) F) =
                !![((ε : 𝓞 F) : F), ((β : 𝓞 F) : F); 0, (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)]) ∧
          globalPoints (𝓞 F) F δ * g ∈ centreCutSiegelSetAmple F (θ * c) R d₁ d₂ κ := by
  classical
  obtain ⟨C, hC⟩ := NumberField.Units.exists_forall_abs_two_mul_log_add_log_sub_div_le F
  obtain ⟨R, hR0, hred⟩ := Ws23.Cover.exists_int_translate_le F
  set C₀ : ℝ := max C 0 with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  refine ⟨Real.exp (2 * C₀), R, Real.exp (-C₀), Real.one_le_exp (by positivity), Real.exp_pos _,
    fun c u d₁ d₂ g hg => ?_⟩
  rw [mem_centreCutSiegelSet_iff] at hg
  obtain ⟨hint, hfloor, hwin, hdet⟩ := hg

  set hgt : InfinitePlace F → ℝ := fun w => localHeight (archComponent F w (glArch (𝓞 F) F g)) with hhgt
  have hpos : ∀ w, 0 < hgt w := fun w => localHeight_pos _

  obtain ⟨ε, hε⟩ := hC hgt hpos
  set m : ℝ := (∑ w' : InfinitePlace F, (w'.mult : ℝ) * Real.log (hgt w')) / (Module.finrank ℚ F) with hm
  have hε' : ∀ w : InfinitePlace F, |2 * Real.log (w ((ε : 𝓞 F) : F)) + Real.log (hgt w) - m| ≤ C₀ := fun w =>
    (hε w).trans (le_max_left _ _)
  have hwε : ∀ w : InfinitePlace F, 0 < w ((ε : 𝓞 F) : F) := fun w =>
    (InfinitePlace.pos_iff).mpr (by exact_mod_cast ε.ne_zero)

  set y : InfinitePlace F → ℂ := fun w =>
    (InfinitePlace.Completion.extensionEmbedding w ((((ε : 𝓞 F) : F)) : w.Completion)) ^ 2 *
      xCoord (((archComponent F w (glArch (𝓞 F) F g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).map (InfinitePlace.Completion.extensionEmbedding w)) with hydef
  have hyreal : ∀ w : InfinitePlace F, w.IsReal → (y w).im = 0 := by
    intro w hw
    have h1 : (InfinitePlace.Completion.extensionEmbedding w ((((ε : 𝓞 F) : F)) : w.Completion)).im = 0 :=
      im_extensionEmbedding_of_isReal F hw _
    have h2 : (xCoord (((archComponent F w (glArch (𝓞 F) F g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).map (InfinitePlace.Completion.extensionEmbedding w))).im = 0 :=
      im_xCoord_eq_zero _ (fun i j => by rw [Matrix.map_apply]; exact im_extensionEmbedding_of_isReal F hw _)
    rw [hydef]; dsimp only
    rw [Complex.mul_im, h2, sq, Complex.mul_im, h1]
    ring
  obtain ⟨b, hb⟩ := hred y hyreal
  set β : 𝓞 F := ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * b with hβ
  refine ⟨delta F ε β, ⟨ε, β, delta_coe F ε β⟩, ?_⟩

  have hεF : (((ε : 𝓞 F) : F)) ≠ 0 := by exact_mod_cast ε.ne_zero
  have hfacts : ∀ w : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F (delta F ε β) * g))) =
          w ((ε : 𝓞 F) : F) ^ 2 * hgt w ∧
      archDetNorm w (globalPoints (𝓞 F) F (delta F ε β) * g) = archDetNorm w g ∧
      xWindowSq (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F (delta F ε β) * g))) =
        ‖y w + (w.embedding : F →+* ℂ) (b : F)‖ ^ 2 := by
    intro w
    set φ := InfinitePlace.Completion.extensionEmbedding w with hφ
    have hφn : ∀ x, ‖φ x‖ = ‖x‖ := norm_extensionEmbedding w
    set s : GL (Fin 2) w.Completion := archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F (delta F ε β))) with hs
    have hmul : archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F (delta F ε β) * g)) =
        s * archComponent F w (glArch (𝓞 F) F g) := by rw [map_mul, map_mul]
    have hsij : ∀ i j, ((s : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j =
        ((!![((ε : 𝓞 F) : F), ((β : 𝓞 F) : F); 0, (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)] : Matrix (Fin 2) (Fin 2) F) i j :
          w.Completion) := by
      intro i j
      rw [hs, archComponent_globalPoints_apply, delta_coe]
    have h00 : ((s : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = ((((ε : 𝓞 F) : F)) : w.Completion) := by
      rw [hsij]; simp
    have h01 : ((s : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = ((((β : 𝓞 F) : F)) : w.Completion) := by
      rw [hsij]; simp
    have h10 : ((s : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
      rw [hsij]; simp [NumberField.InfinitePlace.Completion.ext_iff]
    have h11 : ((s : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 =
        (((((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) : w.Completion) := by
      rw [hsij]; simp
    have hεw : ((((ε : 𝓞 F) : F)) : w.Completion) ≠ 0 := by
      rw [← norm_pos_iff, norm_coe_completion]; exact hwε w

    have htaF : ((((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) * (((ε : 𝓞 F) : F)) = 1 := by
      rw [unit_inv_coe, inv_mul_cancel₀ hεF]
    have hta : (((((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) : w.Completion) * ((((ε : 𝓞 F) : F)) : w.Completion) = 1 := by
      have h := congrArg (algebraMap F w.Completion) htaF
      rw [map_mul, map_one] at h
      exact h
    have hεw' : (((((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) : w.Completion) ≠ 0 := left_ne_zero_of_mul_eq_one hta
    have hnormt : ‖(((((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) : w.Completion)‖ = (w ((ε : 𝓞 F) : F))⁻¹ := by
      rw [norm_coe_completion, unit_inv_coe, map_inv₀]
    refine ⟨?_, ?_, ?_⟩
    ·
      rw [hmul, localHeight_upper_entries_mul hεw' h00 h10 h11, norm_coe_completion, hnormt, div_inv_eq_mul, sq]
    ·
      unfold archDetNorm
      rw [hmul, det_upper_entries_mul h00 h10 h11, norm_mul, norm_mul, norm_coe_completion, hnormt,
        mul_inv_cancel₀ (hwε w).ne', one_mul]
    ·
      rw [hmul, xWindowSq_eq_norm_xCoord_map_sq φ hφn, ← coe_map φ, map_mul]
      have hφt : φ (((((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) : w.Completion) = (φ ((((ε : 𝓞 F) : F)) : w.Completion))⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← map_mul, hta, map_one])
      have hx := xCoord_upper_entries_mul (s := Matrix.GeneralLinearGroup.map φ s)
        (g := Matrix.GeneralLinearGroup.map φ (archComponent F w (glArch (𝓞 F) F g)))
        (a := φ ((((ε : 𝓞 F) : F)) : w.Completion)) (b := φ ((((β : 𝓞 F) : F)) : w.Completion))
        (t := φ (((((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) : w.Completion)) (by rw [map_ne_zero]; exact hεw')
        (by rw [coe_map, Matrix.map_apply, h00]) (by rw [coe_map, Matrix.map_apply, h01])
        (by rw [coe_map, Matrix.map_apply, h10, map_zero]) (by rw [coe_map, Matrix.map_apply, h11])
      rw [hx, coe_map, hφt, div_eq_mul_inv, inv_inv, div_eq_mul_inv, inv_inv, ← sq, ← map_mul, hydef]
      dsimp only
      congr 2

      have hbF : (((β : 𝓞 F) : F)) * (((ε : 𝓞 F) : F)) = ((b : 𝓞 F) : F) := by
        have h1 := htaF
        rw [hβ]
        push_cast at h1 ⊢
        rw [mul_right_comm, h1, one_mul]
      have hbC : ((((β : 𝓞 F) : F)) : w.Completion) * ((((ε : 𝓞 F) : F)) : w.Completion) = (((b : 𝓞 F) : F) : w.Completion) := by
        have h := congrArg (algebraMap F w.Completion) hbF
        rw [map_mul] at h
        exact h
      rw [hbC]
      simp [hφ]

  rw [mem_centreCutSiegelSetAmple_iff, mem_centreCutSiegelSet_iff]
  have hlogh : ∀ w : InfinitePlace F, Real.log (w ((ε : 𝓞 F) : F) ^ 2 * hgt w) =
      2 * Real.log (w ((ε : 𝓞 F) : F)) + Real.log (hgt w) := fun w => by
    rw [Real.log_mul (pow_ne_zero 2 (hwε w).ne') (hpos w).ne', Real.log_pow]; push_cast; ring
  have hnewpos : ∀ w : InfinitePlace F, 0 < w ((ε : 𝓞 F) : F) ^ 2 * hgt w := fun w => mul_pos (pow_pos (hwε w) 2) (hpos w)
  have hup : ∀ w : InfinitePlace F, Real.log (w ((ε : 𝓞 F) : F) ^ 2 * hgt w) ≤ m + C₀ := fun w => by
    rw [hlogh]; have := hε' w; rw [abs_le] at this; linarith [this.2]
  have hdown : ∀ w : InfinitePlace F, m - C₀ ≤ Real.log (w ((ε : 𝓞 F) : F) ^ 2 * hgt w) := fun w => by
    rw [hlogh]; have := hε' w; rw [abs_le] at this; linarith [this.1]
  refine ⟨⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩, fun w w' => ?_⟩
  ·
    simp only [map_mul]
    exact Subgroup.mul_mem _ (glFin_globalPoints_delta_mem F ε β) hint
  ·
    rw [(hfacts w).1]
    rcases le_or_gt c 0 with hc | hc
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hc |>.trans le_rfl) (hnewpos w).le
    ·
      have hmc : Real.log c ≤ m := by
        rw [hm, le_div_iff₀ (by exact_mod_cast Module.finrank_pos (R := ℚ) (M := F))]
        have hsum : ∑ w' : InfinitePlace F, (w'.mult : ℝ) * Real.log c ≤
            ∑ w' : InfinitePlace F, (w'.mult : ℝ) * Real.log (hgt w') :=
          Finset.sum_le_sum fun w' _ => mul_le_mul_of_nonneg_left
            (Real.log_le_log hc (hfloor w')) (Nat.cast_nonneg _)
        rw [← Finset.sum_mul] at hsum
        have hcard : (∑ w' : InfinitePlace F, (w'.mult : ℝ)) = (Module.finrank ℚ F : ℝ) := by
          exact_mod_cast NumberField.InfinitePlace.sum_mult_eq (K := F)
        rw [hcard] at hsum
        linarith
      rw [← Real.log_le_log_iff (mul_pos (Real.exp_pos _) hc) (hnewpos w), Real.log_mul (Real.exp_pos _).ne' hc.ne',
        Real.log_exp]
      linarith [hdown w]
  ·
    rw [(hfacts w).2.2]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb w) 2
  ·
    rw [(hfacts w).2.1]
    exact hdet w
  ·
    rw [(hfacts w).1, (hfacts w').1]
    rw [← Real.log_le_log_iff (hnewpos w) (mul_pos (Real.exp_pos _) (hnewpos w')),
      Real.log_mul (Real.exp_pos _).ne' (hnewpos w').ne', Real.log_exp]
    linarith [hup w, hdown w']

end Main

end Ws23.Cover

end

open IsDedekindDomain NumberField Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ κ R θ : ℝ, 1 ≤ κ ∧ 0 < θ ∧
      ∀ (c u d₁ d₂ : ℝ), ∀ g ∈ centreCutSiegelSet K c u d₁ d₂,
        ∃ δ : GL (Fin 2) K,
          (∃ (ε : (𝓞 K)ˣ) (β : 𝓞 K),
              (δ : Matrix (Fin 2) (Fin 2) K) =
                !![((ε : 𝓞 K) : K), ((β : 𝓞 K) : K); 0, (((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)]) ∧
          globalPoints (𝓞 K) K δ * g ∈ centreCutSiegelSetAmple K (θ * c) R d₁ d₂ κ :=
  Ws23.Cover.main K

end S_AutomorphicForm_exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple (solution)
