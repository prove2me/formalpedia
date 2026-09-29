-- Prove2me | solution 1 for AutomorphicForm.exists_coversModCentre_centreCutSiegelSetAmple
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/84548558-334a-52a1-87d0-a80994754364

import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_SiegelReduction
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple

set_option autoImplicit false
set_option maxHeartbeats 1600000

open NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

noncomputable section

namespace Ws1
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

end Ws1.Cover

open Ws1.Cover AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction NumberField.InfinitePlace NumberField.AdelicVolume in

theorem solution
    (F : Type) [Field F] [NumberField F] :
    ∃ κ R : ℝ, 1 ≤ κ ∧ 0 ≤ R ∧
      ∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)),
        CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) →
        CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c (max u R) d₁ d₂ κ) := by
  classical
  obtain ⟨ρ, hρ0, hbal⟩ := Ws1.Cover.exists_unit_log_balance F
  obtain ⟨R, hR0, hred⟩ := Ws1.Cover.exists_int_translate_le F
  obtain ⟨dd, hdd⟩ : ∃ dd : ℝ, dd = ∑ w : InfinitePlace F, (w.mult : ℝ) := ⟨_, rfl⟩
  have hmult1 : ∀ w : InfinitePlace F, (1 : ℝ) ≤ w.mult := fun w => by exact_mod_cast (mult_pos (w := w))
  have hdd1 : 1 ≤ dd := by
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
    rw [hdd]
    exact le_trans (hmult1 w₀) (Finset.single_le_sum (fun w _ => le_trans zero_le_one (hmult1 w)) (Finset.mem_univ w₀))
  have hdd0 : 0 < dd := lt_of_lt_of_le one_pos hdd1
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = Real.exp (max 2 dd * ρ) := ⟨_, rfl⟩
  have hκ1 : 1 ≤ κ := by rw [hκ]; exact Real.one_le_exp (mul_nonneg (le_trans zero_le_two (le_max_left _ _)) hρ0)
  have hκ0 : 0 < κ := by rw [hκ]; exact Real.exp_pos _
  have hlogκ : Real.log κ = max 2 dd * ρ := by rw [hκ, Real.log_exp]
  have h2ρ : 2 * ρ ≤ Real.log κ := by rw [hlogκ]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hρ0
  have hdρ : dd * ρ ≤ Real.log κ := by rw [hlogκ]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hρ0
  refine ⟨κ, R, hκ1, hR0, fun c u d₁ d₂ T hcov g => ?_⟩

  obtain ⟨γ, z, hγ⟩ := hcov g
  simp only [Set.mem_iUnion, Set.mem_image] at hγ
  obtain ⟨x, hxT, s, hs, hsx⟩ := hγ
  rw [mem_centreCutSiegelSet_iff] at hs
  obtain ⟨hint, hfloor, hwin, hdet⟩ := hs
  obtain ⟨hgt, hhgt⟩ : ∃ hgt : InfinitePlace F → ℝ, hgt = fun w => localHeight (archComponent F w (glArch (𝓞 F) F s)) := ⟨_, rfl⟩
  have hhgtw : ∀ w, hgt w = localHeight (archComponent F w (glArch (𝓞 F) F s)) := fun w => by rw [hhgt]
  have hpos : ∀ w, 0 < hgt w := fun w => by rw [hhgtw]; exact localHeight_pos _

  have hε : ∃ ε : (𝓞 F)ˣ, (∀ w w' : InfinitePlace F, w ((ε : 𝓞 F) : F) * hgt w ≤ κ * (w' ((ε : 𝓞 F) : F) * hgt w')) ∧
      ∀ w : InfinitePlace F, c ≤ w ((ε : 𝓞 F) : F) * hgt w := by
    by_cases hcomp : ∀ w w' : InfinitePlace F, hgt w ≤ κ * hgt w'
    · refine ⟨1, fun w w' => ?_, fun w => ?_⟩
      · simp only [Units.val_one, OneMemClass.coe_one, map_one, one_mul]
        exact hcomp w w'
      · simp only [Units.val_one, OneMemClass.coe_one, map_one, one_mul]
        rw [hhgtw]; exact hfloor w
    · push Not at hcomp
      obtain ⟨w₁, w₂, hlt⟩ := hcomp
      obtain ⟨ε, hεb⟩ := hbal (fun w => Real.log (hgt w))
      obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (∑ w' : InfinitePlace F, (w'.mult : ℝ) * Real.log (hgt w')) /
          (∑ w' : InfinitePlace F, (w'.mult : ℝ)) := ⟨_, rfl⟩
      have hwε : ∀ w : InfinitePlace F, 0 < w ((ε : 𝓞 F) : F) := fun w =>
        (InfinitePlace.pos_iff).mpr (by exact_mod_cast ε.ne_zero)
      have hlog : ∀ w : InfinitePlace F, Real.log (w ((ε : 𝓞 F) : F) * hgt w) = Real.log (hgt w) + Real.log (w ((ε : 𝓞 F) : F)) := by
        intro w; rw [Real.log_mul (hwε w).ne' (hpos w).ne', add_comm]
      have hup : ∀ w : InfinitePlace F, Real.log (w ((ε : 𝓞 F) : F) * hgt w) ≤ m + ρ := fun w => by
        rw [hlog]; have := hεb w; rw [← hm, abs_le] at this; linarith [this.2]
      have hdown : ∀ w : InfinitePlace F, m - ρ ≤ Real.log (w ((ε : 𝓞 F) : F) * hgt w) := fun w => by
        rw [hlog]; have := hεb w; rw [← hm, abs_le] at this; linarith [this.1]
      refine ⟨ε, fun w w' => ?_, fun w => ?_⟩
      ·
        have hpw : 0 < w ((ε : 𝓞 F) : F) * hgt w := mul_pos (hwε w) (hpos w)
        have hpw' : 0 < w' ((ε : 𝓞 F) : F) * hgt w' := mul_pos (hwε w') (hpos w')
        rw [← Real.log_le_log_iff hpw (mul_pos hκ0 hpw'), Real.log_mul hκ0.ne' hpw'.ne']
        linarith [hup w, hdown w']
      ·
        rcases le_or_gt c 0 with hc | hc
        · exact le_trans hc (mul_pos (hwε w) (hpos w)).le
        ·
          have hlogc : ∀ w' : InfinitePlace F, Real.log c ≤ Real.log (hgt w') := fun w' =>
            Real.log_le_log hc (by rw [hhgtw]; exact hfloor w')
          have hw₁ : Real.log c + Real.log κ ≤ Real.log (hgt w₁) := by
            have h1 : κ * c ≤ κ * hgt w₂ := mul_le_mul_of_nonneg_left (by rw [hhgtw]; exact hfloor w₂) hκ0.le
            have h2 : κ * c < hgt w₁ := lt_of_le_of_lt h1 hlt
            rw [← Real.log_mul hc.ne' hκ0.ne', mul_comm]
            exact (Real.log_le_log (mul_pos hκ0 hc) h2.le)
          have hsum : dd * Real.log c + Real.log κ ≤ ∑ w' : InfinitePlace F, (w'.mult : ℝ) * Real.log (hgt w') := by
            rw [hdd, Finset.sum_mul, Fintype.sum_eq_add_sum_subtype_ne _ w₁,
              Fintype.sum_eq_add_sum_subtype_ne (fun w' : InfinitePlace F => (w'.mult : ℝ) * Real.log (hgt w')) w₁]
            have hA : (w₁.mult : ℝ) * Real.log c + Real.log κ ≤ (w₁.mult : ℝ) * Real.log (hgt w₁) := by
              have := mul_le_mul_of_nonneg_left hw₁ (le_trans zero_le_one (hmult1 w₁))
              have hk : Real.log κ ≤ (w₁.mult : ℝ) * Real.log κ :=
                le_mul_of_one_le_left (by rw [hlogκ]; positivity) (hmult1 w₁)
              linarith
            have hB : ∑ w' : {w' : InfinitePlace F // w' ≠ w₁}, (w'.1.mult : ℝ) * Real.log c ≤
                ∑ w' : {w' : InfinitePlace F // w' ≠ w₁}, (w'.1.mult : ℝ) * Real.log (hgt w'.1) :=
              Finset.sum_le_sum fun w' _ => mul_le_mul_of_nonneg_left (hlogc w'.1) (le_trans zero_le_one (hmult1 w'.1))
            linarith
          have hmlow : Real.log c + ρ ≤ m := by
            rw [hm, ← hdd, le_div_iff₀ hdd0]
            nlinarith [hsum, hdρ, hdd0]
          have := hdown w
          have hpw : 0 < w ((ε : 𝓞 F) : F) * hgt w := mul_pos (hwε w) (hpos w)
          rw [← Real.log_le_log_iff hc hpw]
          linarith
  obtain ⟨ε, hratio, hfloor'⟩ := hε
  have hwε : ∀ w : InfinitePlace F, 0 < w ((ε : 𝓞 F) : F) := fun w =>
    (InfinitePlace.pos_iff).mpr (by exact_mod_cast ε.ne_zero)

  obtain ⟨y, hydef⟩ : ∃ y : InfinitePlace F → ℂ, y = fun w => InfinitePlace.Completion.extensionEmbedding w ((((ε : 𝓞 F) : F)) : w.Completion) *
    xCoord (((archComponent F w (glArch (𝓞 F) F s) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).map
      (InfinitePlace.Completion.extensionEmbedding w)) := ⟨_, rfl⟩
  have hyreal : ∀ w : InfinitePlace F, w.IsReal → (y w).im = 0 := by
    intro w hw
    rw [hydef]; dsimp only
    rw [Complex.mul_im, im_extensionEmbedding_of_isReal F hw, im_xCoord_eq_zero _ (fun i j => ?_), mul_zero, zero_mul,
      add_zero]
    rw [Matrix.map_apply]
    exact im_extensionEmbedding_of_isReal F hw _
  obtain ⟨β, hβ⟩ := hred y hyreal

  obtain ⟨aval, haval⟩ : ∃ aval : ∀ w : InfinitePlace F, w.Completion, aval = fun w => ofRealAt F w (Real.sqrt (w ((ε : 𝓞 F) : F))⁻¹) := ⟨_, rfl⟩
  have ha0 : ∀ w, aval w ≠ 0 := fun w => by
    rw [← norm_pos_iff, haval]; dsimp only
    rw [norm_ofRealAt, abs_of_pos (Real.sqrt_pos.mpr (inv_pos.mpr (hwε w)))]
    exact Real.sqrt_pos.mpr (inv_pos.mpr (hwε w))
  obtain ⟨a, ha⟩ : ∃ a : ∀ w : InfinitePlace F, (w.Completion)ˣ, a = fun w => Units.mk0 (aval w) (ha0 w) := ⟨_, rfl⟩
  have hnorma : ∀ w, ‖(a w : w.Completion)‖ ^ 2 = (w ((ε : 𝓞 F) : F))⁻¹ := fun w => by
    rw [ha]; dsimp only; rw [Units.val_mk0, haval]; dsimp only
    rw [norm_ofRealAt, sq_abs, Real.sq_sqrt (inv_pos.mpr (hwε w)).le]

  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : GL (Fin 2) F, γ₀ = unipotentGL2 ((β : F)) * diagOne (unitF F ε) := ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z' : (AdeleRing (𝓞 F) F)ˣ, z' = archIdele F a := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s' : AdelicGL2 (𝓞 F) F, s' = centralScalar (𝓞 F) F z' * (globalPoints (𝓞 F) F γ₀ * s) := ⟨_, rfl⟩
  refine ⟨γ₀ * γ, z * z', ?_⟩
  have hnew : globalPoints (𝓞 F) F (γ₀ * γ) * g * centralScalar (𝓞 F) F (z * z') = s' * x := by
    rw [map_mul, map_mul, hs']
    calc globalPoints (𝓞 F) F γ₀ * globalPoints (𝓞 F) F γ * g * (centralScalar (𝓞 F) F z * centralScalar (𝓞 F) F z')
        = globalPoints (𝓞 F) F γ₀ * (globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z) * centralScalar (𝓞 F) F z' := by
          simp only [mul_assoc]
      _ = globalPoints (𝓞 F) F γ₀ * (s * x) * centralScalar (𝓞 F) F z' := by rw [hsx]
      _ = globalPoints (𝓞 F) F γ₀ * s * (x * centralScalar (𝓞 F) F z') := by simp only [mul_assoc]
      _ = globalPoints (𝓞 F) F γ₀ * s * (centralScalar (𝓞 F) F z' * x) := by rw [mul_centralScalar_comm]
      _ = (globalPoints (𝓞 F) F γ₀ * s) * centralScalar (𝓞 F) F z' * x := by simp only [mul_assoc]
      _ = centralScalar (𝓞 F) F z' * (globalPoints (𝓞 F) F γ₀ * s) * x := by rw [mul_centralScalar_comm]
  rw [hnew]
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨x, hxT, s', ?_, rfl⟩

  have hγ₀c := redElt_coe F ε β
  have hfacts : ∀ w : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F s')) = w ((ε : 𝓞 F) : F) * hgt w ∧
      archDetNorm w s' = archDetNorm w s ∧
      xWindowSq (archComponent F w (glArch (𝓞 F) F s')) = ‖y w + (w.embedding : F →+* ℂ) (β : F)‖ ^ 2 := by
    intro w
    have hcomp : archComponent F w (glArch (𝓞 F) F s') =
        archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z')) *
          (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ₀)) * archComponent F w (glArch (𝓞 F) F s)) := by
      rw [hs', map_mul, map_mul, map_mul, map_mul]
    obtain ⟨hZ00, hZ01, hZ10, hZ11⟩ := archComponent_centralScalar_archIdele F w a
    rw [← hz'] at hZ00 hZ01 hZ10 hZ11
    have hU : ∀ i j, (((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ₀))) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j = ((!![((ε : 𝓞 F) : F), (β : F); 0, 1] : Matrix (Fin 2) (Fin 2) F) i j : w.Completion) := by
      intro i j
      rw [archComponent_globalPoints_apply, hγ₀, hγ₀c]
    have hεw : ((((ε : 𝓞 F) : F)) : w.Completion) ≠ 0 := by
      rw [← norm_pos_iff, norm_coe_completion]; exact hwε w
    obtain ⟨h1, h2, h3⟩ := step_place F w (archComponent F w (glArch (𝓞 F) F s))
      (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ₀)))
      (archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z')))
      ((((ε : 𝓞 F) : F)) : w.Completion) (((β : F)) : w.Completion) (a w : w.Completion) hεw (a w).ne_zero
      (by rw [hU]; simp) (by rw [hU]; simp)
      (by rw [hU]; simp [NumberField.InfinitePlace.Completion.ext_iff])
      (by rw [hU]; simp [NumberField.InfinitePlace.Completion.ext_iff])
      hZ00 hZ01 hZ10 hZ11
    rw [← hcomp] at h1 h2 h3
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, norm_coe_completion, hhgtw]
    · unfold archDetNorm
      rw [h2, hnorma, norm_coe_completion, inv_mul_cancel₀ (hwε w).ne', one_mul]
    · rw [h3, hydef]
      dsimp only
      congr 2
      simp

  rw [mem_centreCutSiegelSetAmple_iff, mem_centreCutSiegelSet_iff]
  refine ⟨⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩, fun w w' => ?_⟩
  ·
    rw [hs', map_mul, map_mul, hz', glFin_centralScalar_archIdele, one_mul, hγ₀, map_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (glFin_globalPoints_unipotentGL2_mem F β)
      (glFin_globalPoints_diagOne_mem F ε)) hint
  ·
    rw [(hfacts w).1]
    exact hfloor' w
  ·
    rw [(hfacts w).2.2]
    calc ‖y w + (w.embedding : F →+* ℂ) (β : F)‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hβ w) 2
      _ ≤ (max u R) ^ 2 := pow_le_pow_left₀ hR0 (le_max_right _ _) 2
  ·
    rw [(hfacts w).2.1]
    exact hdet w
  ·
    rw [(hfacts w).1, (hfacts w').1]
    exact hratio w w'

end
end S_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple
end P2MW
export P2MW.S_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple (solution)
