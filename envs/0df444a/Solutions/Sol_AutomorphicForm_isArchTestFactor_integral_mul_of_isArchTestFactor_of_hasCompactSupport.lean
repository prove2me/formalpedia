-- Prove2me | solution 1 for AutomorphicForm.isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2666bdbd-665d-5bd9-99e3-9d12a4a8fc11

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicBox
import Mathlib.Analysis.Calculus.ParametricIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport

set_option autoImplicit false

open NumberField MeasureTheory AutomorphicForm
open scoped Topology Pointwise ContDiff Classical

noncomputable section

namespace ARCHCONV

section Parametric

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]
  (η : Y → P) (hη : Continuous η) {K : Set Y} (hK : IsCompact K)

def D1 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Λ : X × P → E) : X × P → (X →L[ℝ] E) :=
  fun p => (fderiv ℝ Λ p).comp (ContinuousLinearMap.inl ℝ X P)

omit [FiniteDimensional ℝ X] in
theorem contDiff_D1 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Λ : X × P → E} (hΛ : ContDiff ℝ ∞ Λ) :
    ContDiff ℝ ∞ (D1 Λ) :=
  (hΛ.fderiv_right le_rfl).clm_comp contDiff_const

omit [FiniteDimensional ℝ X] in
theorem hasFDerivAt_D1 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Λ : X × P → E} (hΛ : ContDiff ℝ ∞ Λ)
    (M : X) (p : P) : HasFDerivAt (fun M => Λ (M, p)) (D1 Λ (M, p)) M :=
  (hΛ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp M (hasFDerivAt_prodMk_left M p)

omit [FiniteDimensional ℝ X] in

theorem D1_vanish {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Λ : X × P → E} (hΛ : ContDiff ℝ ∞ Λ)
    (hvan : ∀ a, a ∉ K → ∀ M, Λ (M, η a) = 0) : ∀ a, a ∉ K → ∀ M, D1 Λ (M, η a) = 0 := by
  intro a ha M
  have h0 : (fun M => Λ (M, η a)) = fun _ => 0 := funext fun M => hvan a ha M
  have h1 := hasFDerivAt_D1 hΛ M (η a)
  rw [h0] at h1
  exact h1.unique (hasFDerivAt_const 0 M)

include hη hK in

theorem hasFDerivAt_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Λ : X × P → E} (hΛ : ContDiff ℝ ∞ Λ) (hvan : ∀ a, a ∉ K → ∀ M, Λ (M, η a) = 0) (M₀ : X) :
    HasFDerivAt (fun M => ∫ a, Λ (M, η a) ∂μ) (∫ a, D1 Λ (M₀, η a) ∂μ) M₀ := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  haveI : ProperSpace X := FiniteDimensional.proper ℝ X
  have hΛc : Continuous Λ := hΛ.continuous
  have hD1c : Continuous (D1 Λ) := (contDiff_D1 hΛ).continuous

  obtain ⟨B, hB⟩ := ((isCompact_closedBall M₀ 1).prod hK).exists_bound_of_continuousOn
    (f := fun p : X × Y => D1 Λ (p.1, η p.2))
    (hD1c.comp (continuous_fst.prodMk (hη.comp continuous_snd))).continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ) (s := Metric.ball M₀ 1)
    (F := fun M a => Λ (M, η a)) (F' := fun M a => D1 Λ (M, η a)) (bound := K.indicator fun _ => B)
    (Metric.ball_mem_nhds M₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun M => (hΛc.comp (continuous_const.prodMk hη)).aestronglyMeasurable
  · exact (hΛc.comp (continuous_const.prodMk hη)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun a ha => hvan a ha M₀)
  · exact (hD1c.comp (continuous_const.prodMk hη)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun a M hM => ?_
    by_cases ha : a ∈ K
    · show ‖D1 Λ (M, η a)‖ ≤ K.indicator (fun _ => B) a
      rw [Set.indicator_of_mem ha]
      exact hB (M, a) ⟨Metric.ball_subset_closedBall hM, ha⟩
    · show ‖D1 Λ (M, η a)‖ ≤ K.indicator (fun _ => B) a
      rw [Set.indicator_of_notMem ha, D1_vanish η hΛ hvan a ha M, norm_zero]
  · exact (integrableOn_const (hK.measure_lt_top (μ := μ)).ne).integrable_indicator hK.measurableSet
  · exact Filter.Eventually.of_forall fun a M _ => hasFDerivAt_D1 hΛ M (η a)

include hη hK in

theorem contDiff_integral (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {Λ : X × P → E} (_ : ContDiff ℝ ∞ Λ) (_ : ∀ a, a ∉ K → ∀ M, Λ (M, η a) = 0),
      ContDiff ℝ n (fun M => ∫ a, Λ (M, η a) ∂μ) := by
  induction n with
  | zero =>
    intro E _ _ _ Λ hΛ hvan
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun M =>
      (hasFDerivAt_integral μ η hη hK hΛ hvan M).continuousAt)
  | succ n ih =>
    intro E _ _ _ Λ hΛ hvan
    have hderiv := fun M => hasFDerivAt_integral μ η hη hK hΛ hvan M
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl, contDiff_succ_iff_fderiv]
    refine ⟨fun M => (hderiv M).differentiableAt, fun h => absurd h (by simp), ?_⟩
    have hfd : fderiv ℝ (fun M => ∫ a, Λ (M, η a) ∂μ) = fun M => ∫ a, D1 Λ (M, η a) ∂μ :=
      funext fun M => (hderiv M).fderiv
    rw [hfd]
    exact ih (contDiff_D1 hΛ) (D1_vanish η hΛ hvan)

include hη hK in
theorem contDiff_integral_infty {Λ : X × P → ℂ} (hΛ : ContDiff ℝ ∞ Λ) (hvan : ∀ a, a ∉ K → ∀ M, Λ (M, η a) = 0) :
    ContDiff ℝ ∞ (fun M => ∫ a, Λ (M, η a) ∂μ) :=
  contDiff_infty.2 fun n => contDiff_integral μ η hη hK n hΛ hvan

end Parametric

section Arch

variable (F : Type) [Field F] [NumberField F]

scoped instance : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))

abbrev Xm : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

abbrev PP : Type := Xm F × ℂ
scoped instance : NormedAddCommGroup (PP F) := Prod.normedAddCommGroup
scoped instance : NormedSpace ℝ (PP F) := Prod.normedSpace

def mulM (A B : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F :=
  fun i j => ∑ l, A i l * B l j

theorem archEntries_mul (x a : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (x * a) = mulM F (archEntries F x) (archEntries F a) := by
  funext i j
  simp only [mulM, archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

theorem continuous_archEntries' : Continuous (archEntries F) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp (Units.continuous_val.matrix_elem i j)

theorem contDiff_weighted {Φ : Xm F → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (fun p : Xm F × PP F => p.2.2 • Φ (mulM F p.1 p.2.1)) := by
  have hmul : ContDiff ℝ ∞ (fun p : Xm F × PP F => mulM F p.1 p.2.1) := by
    refine contDiff_pi' fun i => contDiff_pi' fun j => ?_
    show ContDiff ℝ ∞ fun p : Xm F × PP F => ∑ l, p.1 i l * p.2.1 l j
    fun_prop
  exact (contDiff_snd.comp contDiff_snd).smul (hΦ.comp hmul)

end Arch

end ARCHCONV
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport.ARCHCONV"

open ARCHCONV in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing F))]
    (μ : Measure (GL (Fin 2) (InfiniteAdeleRing F))) [μ.IsHaarMeasure]
    (fa g : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : IsArchTestFactor F fa) (hg : Continuous g) (hgs : HasCompactSupport g) :
    IsArchTestFactor F (fun x => ∫ a, fa (x * a) * g a ∂μ) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa

  let η : GL (Fin 2) (InfiniteAdeleRing F) → PP F := fun a => (archEntries F a, g a)
  have hη : Continuous η := (continuous_archEntries' F).prodMk hg
  let Λ : Xm F × PP F → ℂ := fun p => p.2.2 • Φ (mulM F p.1 p.2.1)
  have hΛ : ContDiff ℝ ∞ Λ := contDiff_weighted F hΦ
  have hvan : ∀ a, a ∉ tsupport g → ∀ M, Λ (M, η a) = 0 := by
    intro a ha M
    show g a • Φ (mulM F M (archEntries F a)) = 0
    rw [image_eq_zero_of_notMem_tsupport ha, zero_smul]
  refine ⟨⟨fun M => ∫ a, Λ (M, η a) ∂μ, contDiff_integral_infty μ η hη hgs hΛ hvan, fun x => ?_⟩, ?_⟩
  ·
    show (∫ a, fa (x * a) * g a ∂μ) = ∫ a, g a • Φ (mulM F (archEntries F x) (archEntries F a)) ∂μ
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    show fa (x * a) * g a = g a • Φ (mulM F (archEntries F x) (archEntries F a))
    rw [hfaΦ, ← archEntries_mul, smul_eq_mul, mul_comm]
  ·
    refine HasCompactSupport.intro (hsupp.mul hgs.inv) fun x hx => ?_
    have hfun : (fun a => fa (x * a) * g a) = fun _ => 0 := by
      funext a
      by_contra hne
      have hga : g a ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
      have hfb : fa (x * a) ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
      exact hx ⟨x * a, subset_tsupport _ (Function.mem_support.mpr hfb), a⁻¹,
        Set.inv_mem_inv.mpr (subset_tsupport _ (Function.mem_support.mpr hga)), mul_inv_cancel_right x a⟩
    show (∫ a, fa (x * a) * g a ∂μ) = 0
    rw [hfun, integral_zero]

end
end S_AutomorphicForm_isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport
end P2MW
export P2MW.S_AutomorphicForm_isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport (solution)
