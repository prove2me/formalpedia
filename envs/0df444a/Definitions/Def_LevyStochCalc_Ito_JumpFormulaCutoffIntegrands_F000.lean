-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffIntegrands_F000
-- name    : LevyStochCalc_Ito_JumpFormulaCutoffIntegrands_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:05:52.796218+00:00
-- url     : https://prove2.me/theorems/59cc0cf9-6ed5-4a27-81c2-d573ea556f3c
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaCutoffIntegrands
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaCutoffIntegrands. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaExhaustion_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormula_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Cutting a function of time and space off outside a box

Multiplying a function of time and space by the product of a one-dimensional smooth cutoff in
time with a box cutoff in space leaves it, together with its time derivative and its first two
space derivatives, unchanged on a box around the origin, and gives it compact support. Along a
path that stays in a ball over a bounded window the two functions therefore give the same
Itô–Lévy integrands, except at the shifted state `x + γ(s, x, e)` reached by a jump, which needs
its own bound. A càdlàg path is bounded on a compact interval, so the events on which a path
stays in a ball over the window, intersected with those on which the jump coefficient along the
path is bounded uniformly in the mark, exhaust the sample space.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpFormulaCutoff

universe u v

section Cutoff

variable {n : ℕ}

/-- The product of the one-dimensional smooth cutoff in time with the box cutoff in space. -/
noncomputable def timeBoxCut (R : ℝ) (z : ℝ × (Fin n → ℝ)) : ℝ :=
  smoothCut R z.1 * boxCut R z.2
/-- The product of a function of time and space with the time–space cutoff of radius `R`. -/
noncomputable def cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ) (R : ℝ) : ℝ → (Fin n → ℝ) → ℝ :=
  fun s x => u s x * timeBoxCut R (s, x)
theorem uncurry_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ) (R : ℝ) :
    Function.uncurry (cutoffFun₂ u R) = fun z => Function.uncurry u z * timeBoxCut R z := rfl
theorem contDiff_timeBoxCut (R : ℝ) : ContDiff ℝ 2 (timeBoxCut (n := n) R) :=
  ((contDiff_smoothCut R).comp contDiff_fst).mul ((contDiff_boxCut R).comp contDiff_snd)
theorem timeBoxCut_eq_one {R : ℝ} (hR : 0 < R) {z : ℝ × (Fin n → ℝ)} (hz : ‖z‖ ≤ 3 * R / 2) :
    timeBoxCut R z = 1 := by
  rw [Prod.norm_def, max_le_iff] at hz
  rw [timeBoxCut, smoothCut_eq_one hR (by simpa [Real.norm_eq_abs] using hz.1),
    boxCut_eq_one hR hz.2, mul_one]
theorem timeBoxCut_eq_zero {R : ℝ} (hR : 0 < R) {z : ℝ × (Fin n → ℝ)} (hz : 2 * R < ‖z‖) :
    timeBoxCut R z = 0 := by
  rw [Prod.norm_def, lt_max_iff] at hz
  rcases hz with h | h
  · rw [timeBoxCut, smoothCut_eq_zero hR (by simpa [Real.norm_eq_abs] using h.le), zero_mul]
  · rw [timeBoxCut, boxCut_eq_zero hR h, mul_zero]
theorem hasCompactSupport_timeBoxCut {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (timeBoxCut (n := n) R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × (Fin n → ℝ)) (2 * R))
    fun z hz => ?_
  refine timeBoxCut_eq_zero hR ?_
  simpa [Metric.mem_closedBall, dist_eq_norm] using not_le.mp fun h => hz (by simpa using h)
theorem timeBoxCut_eventuallyEq_one {R : ℝ} (hR : 0 < R) {z : ℝ × (Fin n → ℝ)}
    (hz : ‖z‖ < 3 * R / 2) : timeBoxCut (n := n) R =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
  have hopen : IsOpen {w : ℝ × (Fin n → ℝ) | ‖w‖ < 3 * R / 2} :=
    isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact timeBoxCut_eq_one hR hw.le
theorem contDiff_uncurry_cutoffFun₂ {u : ℝ → (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (R : ℝ) :
    ContDiff ℝ 2 (Function.uncurry (cutoffFun₂ u R)) := by
  rw [uncurry_cutoffFun₂]
  exact hu.mul (contDiff_timeBoxCut R)
theorem hasCompactSupport_uncurry_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (Function.uncurry (cutoffFun₂ u R)) := by
  rw [uncurry_cutoffFun₂]
  exact (hasCompactSupport_timeBoxCut hR).mul_left
/-- At a time inside the window the cutoff is the space cutoff of the time slice. -/
theorem cutoffFun₂_slice (u : ℝ → (Fin n → ℝ) → ℝ) {R s : ℝ} (hR : 0 < R)
    (hs : |s| ≤ 3 * R / 2) : cutoffFun₂ u R s = cutoffFun (u s) R := by
  funext x
  simp only [cutoffFun₂, timeBoxCut, cutoffFun, smoothCut_eq_one hR hs, one_mul]
theorem cutoffFun₂_eq {u : ℝ → (Fin n → ℝ) → ℝ} {R s : ℝ} (hR : 0 < R) (hs : |s| ≤ 3 * R / 2)
    {x : Fin n → ℝ} (hx : ‖x‖ ≤ 3 * R / 2) : cutoffFun₂ u R s x = u s x := by
  simp only [cutoffFun₂, timeBoxCut, smoothCut_eq_one hR hs, boxCut_eq_one hR hx, mul_one]
/-- The space gradient of the cutoff agrees with that of the function inside the window. -/
theorem gradient_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ) {R s : ℝ} (hR : 0 < R)
    (hs : |s| ≤ 3 * R / 2) {x : Fin n → ℝ} (hx : ‖x‖ < 3 * R / 2) :
    JumpFormula.gradient (cutoffFun₂ u R) s x = JumpFormula.gradient u s x := by
  funext i
  simp only [JumpFormula.gradient, cutoffFun₂_slice u hR hs, fderiv_cutoffFun hR hx]
/-- The space Hessian of the cutoff agrees with that of the function inside the window. -/
theorem hessian_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ) {R s : ℝ} (hR : 0 < R)
    (hs : |s| ≤ 3 * R / 2) {x : Fin n → ℝ} (hx : ‖x‖ < 3 * R / 2) :
    JumpFormula.hessian (cutoffFun₂ u R) s x = JumpFormula.hessian u s x := by
  have hopen : IsOpen {w : Fin n → ℝ | ‖w‖ < 3 * R / 2} :=
    isOpen_lt continuous_norm continuous_const
  funext i j
  simp only [JumpFormula.hessian, cutoffFun₂_slice u hR hs]
  have hev : (fun y => fderiv ℝ (cutoffFun (u s) R) y (Pi.single i 1))
      =ᶠ[𝓝 x] fun y => fderiv ℝ (u s) y (Pi.single i 1) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [fderiv_cutoffFun hR hy]
  rw [hev.fderiv_eq]
/-- The time derivative of the cutoff agrees with that of the function inside the window. -/
theorem timeDeriv_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ) {R s : ℝ} (hR : 0 < R)
    (hs : |s| < 3 * R / 2) {x : Fin n → ℝ} (hx : ‖x‖ ≤ 3 * R / 2) :
    JumpFormula.timeDeriv (cutoffFun₂ u R) s x = JumpFormula.timeDeriv u s x := by
  have hopen : IsOpen {t : ℝ | |t| < 3 * R / 2} := isOpen_lt continuous_abs continuous_const
  have hev : (fun t => cutoffFun₂ u R t x) =ᶠ[𝓝 s] fun t => u t x := by
    filter_upwards [hopen.mem_nhds hs] with t ht
    exact cutoffFun₂_eq hR (le_of_lt ht) hx
  simp only [JumpFormula.timeDeriv]
  exact hev.deriv_eq
end Cutoff

section Integrands

variable {n d : ℕ} {E : Type v}

/-- The diffusion integrand of the cutoff agrees with that of the function inside the window. -/
theorem diffusionIntegrand_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ)
    (σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)) {R s : ℝ} (hR : 0 < R) (hs : |s| ≤ 3 * R / 2)
    {x : Fin n → ℝ} (hx : ‖x‖ < 3 * R / 2) :
    JumpFormula.diffusionIntegrand (cutoffFun₂ u R) σ s x
      = JumpFormula.diffusionIntegrand u σ s x := by
  funext j
  simp only [JumpFormula.diffusionIntegrand, gradient_cutoffFun₂ u hR hs hx]
/-- The drift integrand of the cutoff agrees with that of the function inside the window. -/
theorem driftIntegrand_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ)
    (coeffs : Setting.JumpDiffusionCoeffs n d E) {R s : ℝ} (hR : 0 < R) (hs : |s| < 3 * R / 2)
    {x : Fin n → ℝ} (hx : ‖x‖ < 3 * R / 2) :
    JumpFormula.driftIntegrand (cutoffFun₂ u R) coeffs s x
      = JumpFormula.driftIntegrand u coeffs s x := by
  simp only [JumpFormula.driftIntegrand, JumpFormula.levyGenerator,
    timeDeriv_cutoffFun₂ u hR hs (le_of_lt hx), gradient_cutoffFun₂ u hR (le_of_lt hs) hx,
    hessian_cutoffFun₂ u hR (le_of_lt hs) hx]
/-- The compensator-drift integrand of the cutoff agrees with that of the function inside the
window, provided the shifted state also lies inside it. -/
theorem compensatorDriftIntegrand_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) {R s : ℝ} (hR : 0 < R) (hs : |s| ≤ 3 * R / 2)
    {x : Fin n → ℝ} (hx : ‖x‖ < 3 * R / 2) (e : E) (hxe : ‖x + γ s x e‖ ≤ 3 * R / 2) :
    JumpFormula.compensatorDriftIntegrand (cutoffFun₂ u R) γ s x e
      = JumpFormula.compensatorDriftIntegrand u γ s x e := by
  simp only [JumpFormula.compensatorDriftIntegrand, gradient_cutoffFun₂ u hR hs hx,
    cutoffFun₂_eq hR hs hxe, cutoffFun₂_eq hR hs (le_of_lt hx)]
/-- The jump integrand of the cutoff agrees with that of the function inside the window,
provided the shifted state also lies inside it. -/
theorem jumpIntegrand_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) {R s : ℝ} (hR : 0 < R) (hs : |s| ≤ 3 * R / 2)
    {x : Fin n → ℝ} (hx : ‖x‖ ≤ 3 * R / 2) (e : E) (hxe : ‖x + γ s x e‖ ≤ 3 * R / 2) :
    cutoffFun₂ u R s (x + γ s x e) - cutoffFun₂ u R s x = u s (x + γ s x e) - u s x := by
  rw [cutoffFun₂_eq hR hs hxe, cutoffFun₂_eq hR hs hx]
end Integrands

section Cadlag

/-- A function that is bounded near every point of a compact interval is bounded on it. -/
theorem exists_bound_of_locally_bounded {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {T : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ M : ℝ, ∀ᶠ s in 𝓝 t, ‖f s‖ ≤ M) :
    ∃ M : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖f s‖ ≤ M := by
  classical
  choose! M hM using h
  obtain ⟨A, -, hcov⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).elim_nhds_subcover
    (fun t => {s : ℝ | ‖f s‖ ≤ M t}) fun t ht => hM t ht
  refine ⟨∑ t ∈ A, |M t|, fun s hs => ?_⟩
  obtain ⟨t, htA, hst⟩ := Set.mem_iUnion₂.1 (hcov hs)
  exact le_trans (le_trans hst (le_abs_self _))
    (Finset.single_le_sum (fun i _ => abs_nonneg (M i)) htA)
/-- Right-continuity at a point together with a left limit there bounds the function on a
neighbourhood of the point. -/
theorem exists_eventually_norm_le {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {t : ℝ} {L : F}
    (hr : Filter.Tendsto f (𝓝[>] t) (𝓝 (f t))) (hl : Filter.Tendsto f (𝓝[<] t) (𝓝 L)) :
    ∃ M : ℝ, ∀ᶠ s in 𝓝 t, ‖f s‖ ≤ M := by
  refine ⟨max (‖f t‖ + 1) (‖L‖ + 1), ?_⟩
  have hlt : ∀ᶠ s in 𝓝[<] t, ‖f s‖ ≤ max (‖f t‖ + 1) (‖L‖ + 1) := by
    filter_upwards [hl.norm.eventually_lt_const (lt_add_one ‖L‖)] with s hs
    exact le_trans hs.le (le_max_right _ _)
  have hgt : ∀ᶠ s in 𝓝[>] t, ‖f s‖ ≤ max (‖f t‖ + 1) (‖L‖ + 1) := by
    filter_upwards [hr.norm.eventually_lt_const (lt_add_one ‖f t‖)] with s hs
    exact le_trans hs.le (le_max_left _ _)
  have hpt : ∀ᶠ s in 𝓝[{t}] t, ‖f s‖ ≤ max (‖f t‖ + 1) (‖L‖ + 1) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [show s = t from hs]
    exact le_trans (by linarith : ‖f t‖ ≤ ‖f t‖ + 1) (le_max_left _ _)
  rw [← nhdsLT_sup_nhdsGE t, ← nhdsGT_sup_nhdsWithin_singleton t]
  exact Filter.eventually_sup.2 ⟨hlt, Filter.eventually_sup.2 ⟨hgt, hpt⟩⟩
/-- A left limit of a path bounded over a window is bounded by the same constant. -/
theorem norm_le_of_tendsto_nhdsLT {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {T M t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) T) {L : F} (hL : Filter.Tendsto f (𝓝[<] t) (𝓝 L))
    (hb : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖f s‖ ≤ M) : ‖L‖ ≤ M := by
  refine le_of_tendsto hL.norm ?_
  have h0 : ∀ᶠ s in 𝓝[<] t, 0 < s :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds ht.1)
  filter_upwards [h0, self_mem_nhdsWithin] with s hs0 hst
  exact hb s ⟨hs0.le, le_trans (le_of_lt hst) ht.2⟩
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- Almost every path of a jump diffusion is bounded over a bounded window. -/
theorem ae_exists_bound_norm (X : Setting.JumpDiffusion W N coeffs x₀) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖X.X s ω‖ ≤ M := by
  filter_upwards [X.cadlag_paths] with ω hω
  refine exists_bound_of_locally_bounded fun t ht => ?_
  obtain ⟨hr, hl⟩ := hω t ht.1
  choose L hL using hl
  exact exists_eventually_norm_le hr (tendsto_pi_nhds.2 hL)
/-- Almost every path of a jump diffusion lies in one member of the exhausting family of events
on which the path stays in a ball over a bounded window. -/
theorem ae_exists_mem_boundedPathSet (X : Setting.JumpDiffusion W N coeffs x₀) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ Brownian.Ito.boundedPathSet X.X T m :=
  Brownian.Ito.ae_exists_mem_boundedPathSet (ae_exists_bound_norm X T)
end Cadlag

section Localising

variable {Ω : Type u} {E : Type v} {n d : ℕ}

/-- The sample points whose jump coefficient along the path is bounded by `m` over `[0, T]`,
uniformly in the mark. -/
def boundedJumpSet (Xp : ℝ → Ω → Fin n → ℝ) (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (T : ℝ)
    (m : ℕ) : Set Ω :=
  {ω : Ω | ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e : E, ‖γ s (Xp s ω) e‖ ≤ (m : ℝ)}
theorem boundedJumpSet_mono (Xp : ℝ → Ω → Fin n → ℝ)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (T : ℝ) {m m' : ℕ} (h : m ≤ m') :
    boundedJumpSet Xp γ T m ⊆ boundedJumpSet Xp γ T m' := fun _ hω s hs e =>
  (hω s hs e).trans (by exact_mod_cast h)
/-- On the `m`-th member of the two exhausting families the cutoff of radius `2m` carries, along
the path and for every mark, the same drift, diffusion, compensator-drift and jump integrands as
the function itself. -/
theorem integrands_cutoffFun₂_eq_of_mem {Xp : ℝ → Ω → Fin n → ℝ}
    {coeffs : Setting.JumpDiffusionCoeffs n d E} (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) {ω : Ω}
    (hb : ω ∈ Brownian.Ito.boundedPathSet Xp T m) (hj : ω ∈ boundedJumpSet Xp coeffs.γ T m)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    JumpFormula.driftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs s (Xp s ω)
          = JumpFormula.driftIntegrand u coeffs s (Xp s ω)
      ∧ JumpFormula.diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω)
          = JumpFormula.diffusionIntegrand u coeffs.σ s (Xp s ω)
      ∧ cutoffFun₂ u (2 * (m : ℝ)) s (Xp s ω) = u s (Xp s ω)
      ∧ (∀ e : E,
          JumpFormula.compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ s
              (Xp s ω) e
            = JumpFormula.compensatorDriftIntegrand u coeffs.γ s (Xp s ω) e)
      ∧ (∀ e : E, cutoffFun₂ u (2 * (m : ℝ)) s (Xp s ω + coeffs.γ s (Xp s ω) e)
              - cutoffFun₂ u (2 * (m : ℝ)) s (Xp s ω)
            = u s (Xp s ω + coeffs.γ s (Xp s ω) e) - u s (Xp s ω)) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  have hsabs : |s| < 3 * (2 * (m : ℝ)) / 2 := by
    rw [hrad, abs_of_nonneg hs.1]
    exact lt_of_le_of_lt hs.2 hTm
  have hxb : ‖Xp s ω‖ ≤ (m : ℝ) := hb s hs
  have hx : ‖Xp s ω‖ < 3 * (2 * (m : ℝ)) / 2 := by rw [hrad]; linarith
  have hxe : ∀ e : E, ‖Xp s ω + coeffs.γ s (Xp s ω) e‖ ≤ 3 * (2 * (m : ℝ)) / 2 := by
    intro e
    refine le_trans (norm_add_le _ _) ?_
    have := hj s hs e
    rw [hrad]
    linarith
  refine ⟨driftIntegrand_cutoffFun₂ u coeffs hR hsabs hx,
    diffusionIntegrand_cutoffFun₂ u coeffs.σ hR (le_of_lt hsabs) hx,
    cutoffFun₂_eq hR (le_of_lt hsabs) (le_of_lt hx), fun e => ?_, fun e => ?_⟩
  · exact compensatorDriftIntegrand_cutoffFun₂ u coeffs.γ hR (le_of_lt hsabs) hx e (hxe e)
  · exact jumpIntegrand_cutoffFun₂ u coeffs.γ hR (le_of_lt hsabs) (le_of_lt hx) e (hxe e)
variable [MeasurableSpace Ω] {P : Measure Ω}

/-- If almost every path carries a jump coefficient bounded over the window, the family of events
on which that bound is `m` covers almost every sample point. -/
theorem ae_exists_mem_boundedJumpSet {Xp : ℝ → Ω → Fin n → ℝ}
    {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)} {T : ℝ}
    (h : ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e : E, ‖γ s (Xp s ω) e‖ ≤ M) :
    ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ boundedJumpSet Xp γ T m := by
  filter_upwards [h] with ω hω
  obtain ⟨M, hM⟩ := hω
  obtain ⟨m, hm⟩ := exists_nat_ge M
  exact ⟨m, fun s hs e => (hM s hs e).trans hm⟩
/-- Two exhausting families and a lower bound on the radius forced by the window combine into a
single exhausting family. -/
theorem ae_exists_mem_inter {Xp : ℝ → Ω → Fin n → ℝ}
    {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)} {T : ℝ}
    (hb : ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ Brownian.Ito.boundedPathSet Xp T m)
    (hj : ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ boundedJumpSet Xp γ T m) :
    ∀ᵐ ω ∂P, ∃ m : ℕ, 0 < m ∧ T < 3 * (m : ℝ) ∧
      ω ∈ Brownian.Ito.boundedPathSet Xp T m ∧ ω ∈ boundedJumpSet Xp γ T m := by
  filter_upwards [hb, hj] with ω hbω hjω
  obtain ⟨m₁, hm₁⟩ := hbω
  obtain ⟨m₂, hm₂⟩ := hjω
  set M : ℕ := max (max m₁ m₂) (⌊T⌋₊ + 1) with hMdef
  have hMge : ⌊T⌋₊ + 1 ≤ M := le_max_right _ _
  have h2 : (⌊T⌋₊ : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hMge
  have h3 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  refine ⟨M, Nat.lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_add_left 1 ⌊T⌋₊) hMge), ?_,
    Brownian.Ito.boundedPathSet_mono Xp T
      (le_trans (le_max_left m₁ m₂) (le_max_left _ _)) hm₁,
    boundedJumpSet_mono Xp γ T (le_trans (le_max_right m₁ m₂) (le_max_left _ _)) hm₂⟩
  linarith [Nat.lt_floor_add_one T]
end Localising

end LevyStochCalc.Ito.JumpFormulaCutoff


