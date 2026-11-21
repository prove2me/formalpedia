-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F002
-- name    : LevyStochCalc_Ito_JumpSplittingAllTimes_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:48:50.091529+00:00
-- url     : https://prove2.me/theorems/65895098-b265-4285-97b5-dbbd77f9cabe
-- title:
--   LevyStochCalc source module: LevyStochCalc.Ito.JumpSplittingAllTimes
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Ito.JumpSplittingAllTimes in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplitting_F001
import Definitions.Def_SourceProof_0daa29c859deac993b505738
import Definitions.Def_SourceProof_231d4b01442d4e78331883f1
import Definitions.Def_SourceProof_6572ebe1e254a873e7002b18
import Definitions.Def_SourceProof_bad7238a06ed14c0fd2ce4b6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The finite-activity splitting at all nonnegative times

The finite-activity splitting of a jump diffusion is an identity between the path, a vector Itô
process and a pathwise jump sum, valid almost surely at each fixed nonnegative time. The jump sum
over `(0, t]` is right-continuous in `t` on a window carrying an integrable jump coefficient and a
jump diffusion has almost surely càdlàg paths, so the identity extends from the nonnegative
rationals to all of `[0, ∞)` on a single set of full measure, for any modification of the vector
Itô process whose paths are right-continuous.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSum_nhdsWithin_Ioi` — right-continuity in time of
  the pathwise jump sum.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_of_ae_rat` — two almost surely right-continuous
  processes agreeing almost surely at each nonnegative rational time agree almost surely at every
  nonnegative time.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSum` — the finite-activity splitting,
  almost surely at all nonnegative times simultaneously.
* `LevyStochCalc.Ito.JumpSplitting.jumpSum_eq_of_measure_zero` — the jump sum is constant across a
  window carrying no mass of the random measure.
* `LevyStochCalc.Ito.JumpSplitting.add_shift_eq_of_ae_forall` — the splitting written as a path
  translated by a shift held fixed strictly between consecutive members of a chain of times.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section Rationals

end Rationals

section Upgrade

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Upgrade

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The jump coefficient along the path of a jump diffusion is almost surely integrable against
the random measure over every bounded window of the mark set. -/
theorem ae_forall_integrableOn_window (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hpred : ∀ i : Fin n,
      Probability.MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (X.X s ω) e i)
    (hγm : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
    (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ) (i : Fin n),
      IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
        (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω) := by
  have hstep : ∀ (m : ℕ) (i : Fin n), ∀ᵐ ω ∂P,
      IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
        (Set.Ioc (0 : ℝ) ((m : ℝ) + 1) ×ˢ A) (N.N ω) := by
    intro m i
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    filter_upwards [_root_.Prove2MeSourceProof.h_6572ebe1e254a873e7002b18 N hℱN hA hAν ((m : ℝ) + 1)
      (hpred i) (hγm i)
      (LevyStochCalc.Poisson.Compensated.window_energy_ne_top
        (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγq i) (A := A) hpos)] with ω hω
    exact hω.1
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun m : ℕ =>
    MeasureTheory.ae_all_iff.mpr fun i : Fin n => hstep m i] with ω hω
  intro T i
  obtain ⟨m, hm⟩ := exists_nat_ge T
  refine (hω m i).mono_set (Set.prod_mono (Set.Ioc_subset_Ioc_right ?_) (subset_refl A))
  linarith
/-- The jump sums over two nested windows differ by the jump sum over the window between them. -/
theorem jumpSum_sub_jumpSum (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    (hA : MeasurableSet A) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {ω : Ω} {i : Fin n}
    (hint : IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
      (Set.Ioc (0 : ℝ) b ×ˢ A) (N.N ω)) :
    jumpSum X A b ω i - jumpSum X A a ω i
      = ∫ q in Set.Ioc a b ×ˢ A, coeffs.γ q.1 (X.X q.1 ω) q.2 i ∂(N.N ω) := by
  have hunion : Set.Ioc (0 : ℝ) b ×ˢ A = Set.Ioc (0 : ℝ) a ×ˢ A ∪ Set.Ioc a b ×ˢ A := by
    rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc ha hab]
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) a ×ˢ A) (Set.Ioc a b ×ˢ A) :=
    Set.disjoint_left.mpr fun q hq hq' => absurd hq.1.2 (not_le.mpr hq'.1.1)
  have h1 : IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
      (Set.Ioc (0 : ℝ) a ×ˢ A) (N.N ω) :=
    hint.mono_set (by rw [hunion]; exact Set.subset_union_left)
  have h2 : IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
      (Set.Ioc a b ×ˢ A) (N.N ω) :=
    hint.mono_set (by rw [hunion]; exact Set.subset_union_right)
  have hsplit : jumpSum X A b ω i
      = jumpSum X A a ω i
        + ∫ q in Set.Ioc a b ×ˢ A, coeffs.γ q.1 (X.X q.1 ω) q.2 i ∂(N.N ω) := by
    simp only [jumpSum]
    rw [hunion, setIntegral_union hdisj (measurableSet_Ioc.prod hA) h1 h2]
  rw [hsplit]
  ring
/-- The jump sum is unchanged across a window on which the random measure carries no mass of the
mark set. -/
theorem jumpSum_eq_of_measure_zero (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    (hA : MeasurableSet A) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {ω : Ω} {i : Fin n}
    (hint : IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
      (Set.Ioc (0 : ℝ) b ×ˢ A) (N.N ω))
    (hzero : (N.N ω) (Set.Ioc a b ×ˢ A) = 0) :
    jumpSum X A b ω i = jumpSum X A a ω i := by
  have h := jumpSum_sub_jumpSum X hA ha hab hint
  rw [setIntegral_measure_zero _ hzero] at h
  linarith
section AllTimes

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X.X s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- **The finite-activity splitting at all nonnegative times.** If the jump coefficient is carried
by a mark set of finite intensity, its integrand along the path is predictable and `V` is a
modification of the vector Itô process with diffusion `σ` and drift `continuousDrift` whose paths
are right-continuous, then almost surely the path is, at every nonnegative time, the sum of `V`
and the pathwise jump sum over that mark set. -/
theorem ae_forall_eq_add_jumpSum
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpred : ∀ i : Fin n,
      Probability.MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (X.X s ω) e i)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDrift X A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Filter.Tendsto (fun s => V s ω i) (nhdsWithin t (Set.Ioi t)) (nhds (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + jumpSum X A t ω i := by
  have hwin := ae_forall_integrableOn_window X ℱ hℱN hA hAν hpred hγm hγq
  have key : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ), 0 ≤ t →
      X.X t ω i = V t ω i + jumpSum X A t ω i := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    refine _root_.Prove2MeSourceProof.h_231d4b01442d4e78331883f1 (P := P) (Y := fun s ω => X.X s ω i)
      (Z := fun s ω => V s ω i + jumpSum X A s ω i) ?_ ?_ ?_
    · intro q hq
      filter_upwards [_root_.Prove2MeSourceProof.h_bad7238a06ed14c0fd2ce4b6 X ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq
        hSDE hA hAν hsupp hpred hμm hμq hq, hVae (q : ℝ) hq] with ω h1 h2
      show X.X (q : ℝ) ω i = V (q : ℝ) ω i + jumpSum X A (q : ℝ) ω i
      rw [h1 i, h2 i]
    · filter_upwards [X.cadlag_paths] with ω hω t ht
      exact ((continuous_apply i).tendsto (X.X t ω)).comp (hω t ht).1
    · filter_upwards [hVright, hwin] with ω hVω hwω t ht
      exact (hVω t ht i).add
        (_root_.Prove2MeSourceProof.h_0daa29c859deac993b505738 X hA (hγm i) (fun T => hwω T i) t)
  filter_upwards [key] with ω hω
  intro t ht i
  exact hω i t ht
end AllTimes

end Setup

end LevyStochCalc.Ito.JumpSplitting


