-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivs_F000
-- name    : LevyStochCalc_Ito_ItoLevyBoundedDerivs_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:39:48.556237+00:00
-- url     : https://prove2.me/theorems/d938f10e-1c97-4c9d-b7aa-e4f17394dafc
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoLevyBoundedDerivs
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoLevyBoundedDerivs. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F001
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy formula for a jump diffusion at bounded derivatives

The Itô–Lévy identity for a `C²` function of time and state whose time derivative, gradient and
Hessian are bounded, along a jump diffusion, with every stochastic integral taken over the one
filtration carried by the SDE data of the solution. The proof is the small-jump truncation: the
big-jump paths at the complements of a spanning family of the intensity are repaired to be
càdlàg at every sample point, the mixed integrands — derivatives of the state function along the
truncated path, coefficients along the solution — are integrated over the right-continuous
filtration, where the truncated paths are adapted, and the four terms are passed to the limit
along one composite subsequence; the two stochastic limits are then transported back to the
filtration of the SDE data.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.truncPath` — the big-jump path at the `m`-th small-mark set,
  restricted to a set of sample points and frozen at zero before time zero.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_boundedDerivs` — the canonical
  residual is the compensated jump integral plus the compensator-drift integral.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section TruncPath

open LevyStochCalc.Ito.BigJump

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

/-- The big-jump path at the `m`-th small-mark set, restricted to a set of sample points and
frozen at zero before time zero. -/
noncomputable def truncPath (S : SdeData X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (G : Set Ω) (m : ℕ) (s : ℝ) (ω : Ω) : Fin n → ℝ :=
  (Set.Ici (0 : ℝ)).indicator
    (fun r => repairOn G (bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0) r ω) s
variable (S : SdeData X)
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
  (G : Set Ω)

theorem truncPath_of_nonneg (m : ℕ) {s : ℝ} (hs : 0 ≤ s) (ω : Ω) :
    truncPath S hℱ0 hnull0 G m s ω
      = repairOn G (bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0) s ω :=
  Set.indicator_of_mem (Set.mem_Ici.mpr hs) _
theorem truncPath_of_neg (m : ℕ) {s : ℝ} (hs : s < 0) (ω : Ω) :
    truncPath S hℱ0 hnull0 G m s ω = 0 :=
  Set.indicator_of_notMem (fun h => absurd (Set.mem_Ici.mp h) (not_le.mpr hs)) _
/-- On the good set and at nonnegative times the truncated path is the big-jump process. -/
theorem truncPath_eq_of_mem (m : ℕ) {s : ℝ} (hs : 0 ≤ s) {ω : Ω} (hω : ω ∈ G) :
    truncPath S hℱ0 hnull0 G m s ω
      = SmallJump.bigJumpProcess S.toJumpIntegrand (measurableSet_smallMarks ν) hℱ0 hnull0
          m s ω := by
  rw [truncPath_of_nonneg S hℱ0 hnull0 G m hs, repairOn_of_mem hω]
  rfl
/-- The truncated path is jointly measurable in the time and the sample point. -/
theorem measurable_uncurry_truncPath (hGm : MeasurableSet G) (m : ℕ) :
    Measurable (Function.uncurry (truncPath S hℱ0 hnull0 G m)) := by
  have hrep := measurable_uncurry_repairOn hGm
    (measurable_uncurry_bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0)
  have heq : Function.uncurry (truncPath S hℱ0 hnull0 G m)
      = {q : ℝ × Ω | 0 ≤ q.1}.indicator (Function.uncurry
          (repairOn G (bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0))) := by
    funext q
    by_cases hq : 0 ≤ q.1
    · change truncPath S hℱ0 hnull0 G m q.1 q.2 = _
      rw [truncPath_of_nonneg S hℱ0 hnull0 G m hq,
        Set.indicator_of_mem (show q ∈ {q : ℝ × Ω | 0 ≤ q.1} from hq)]
      rfl
    · change truncPath S hℱ0 hnull0 G m q.1 q.2 = _
      rw [truncPath_of_neg S hℱ0 hnull0 G m (not_le.mp hq),
        Set.indicator_of_notMem (show q ∉ {q : ℝ × Ω | 0 ≤ q.1} from hq)]
  rw [heq]
  exact hrep.indicator (measurableSet_le measurable_const measurable_fst)
/-- Every path of the truncated path is right-continuous, when the big-jump paths are càdlàg on
the good set. -/
theorem truncPath_rightContinuous
    (hGp : ∀ ω ∈ G, ∀ m : ℕ, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 s ω) (𝓝[>] t)
          (𝓝 (bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ,
          Tendsto (fun s => bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 s ω i)
            (𝓝[<] t) (𝓝 L))
    (m : ℕ) (ω : Ω) (t : ℝ) :
    Tendsto (fun s => truncPath S hℱ0 hnull0 G m s ω) (𝓝[>] t)
      (𝓝 (truncPath S hℱ0 hnull0 G m t ω)) := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [truncPath_of_neg S hℱ0 hnull0 G m ht]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs
    exact (truncPath_of_neg S hℱ0 hnull0 G m (Set.mem_Iio.mp hs) ω).symm
  · rw [truncPath_of_nonneg S hℱ0 hnull0 G m ht]
    have hrep := (repairOn_cadlag (fun ω hω t ht => hGp ω hω m t ht) ω t ht).1
    refine hrep.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (truncPath_of_nonneg S hℱ0 hnull0 G m (ht.trans (le_of_lt (Set.mem_Ioi.mp hs)))
      ω).symm
/-- Every coordinate of every path of the truncated path has a left limit at every time, when
the big-jump paths are càdlàg on the good set. -/
theorem truncPath_leftLim
    (hGp : ∀ ω ∈ G, ∀ m : ℕ, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 s ω) (𝓝[>] t)
          (𝓝 (bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ,
          Tendsto (fun s => bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 s ω i)
            (𝓝[<] t) (𝓝 L))
    (m : ℕ) (ω : Ω) (t : ℝ) (i : Fin n) :
    ∃ L : ℝ, Tendsto (fun s => truncPath S hℱ0 hnull0 G m s ω i) (𝓝[<] t) (𝓝 L) := by
  rcases le_or_gt t 0 with ht | ht
  · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [truncPath_of_neg S hℱ0 hnull0 G m (lt_of_lt_of_le (Set.mem_Iio.mp hs) ht)]
    rfl
  · obtain ⟨L, hL⟩ := (repairOn_cadlag (fun ω hω t ht => hGp ω hω m t ht) ω t ht.le).2 i
    refine ⟨L, hL.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    rw [truncPath_of_nonneg S hℱ0 hnull0 G m hs.1.le]
/-- The truncated path is adapted to the right-continuous filtration of the SDE data, when the
good set belongs to it at every nonnegative time. -/
theorem measurable_rightCont_truncPath (hXadapt : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t))
    (hG : ∀ t : ℝ, 0 ≤ t → MeasurableSet[S.ℱ.rightCont t] G) (m : ℕ) (t : ℝ) :
    Measurable[S.ℱ.rightCont t] (truncPath S hℱ0 hnull0 G m t) := by
  classical
  rcases lt_or_ge t 0 with ht | ht
  · have hz : truncPath S hℱ0 hnull0 G m t = fun _ => 0 :=
      funext fun ω => truncPath_of_neg S hℱ0 hnull0 G m ht ω
    rw [hz]
    exact measurable_const
  · have hite : truncPath S hℱ0 hnull0 G m t = fun ω =>
        if ω ∈ G then bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 t ω else 0 := by
      funext ω
      rw [truncPath_of_nonneg S hℱ0 hnull0 G m ht]
      by_cases hω : ω ∈ G <;> simp [repairOn, hω]
    rw [hite]
    -- The two ingredients, elaborated against the ambient measurable space before the
    -- filtration at `t` is installed as the ambient one.
    have hXm : Measurable[S.ℱ.rightCont t] (X.X t) :=
      (hXadapt t).mono (S.ℱ.le_rightCont t) le_rfl
    have hcut : ∀ i : Fin n, Measurable[S.ℱ.rightCont t]
        (cutJumpIntegral S (measurableSet_smallMarks ν m) hℱ0 hnull0 i t) := fun i =>
      adapted_cutJumpIntegral S (measurableSet_smallMarks ν m) hℱ0 hnull0 i t
    have hGt : MeasurableSet[S.ℱ.rightCont t] G := hG t ht
    have hbig : Measurable[S.ℱ.rightCont t]
        (bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 t) := by
      letI : MeasurableSpace Ω := S.ℱ.rightCont t
      exact measurable_pi_lambda _ fun i => ((measurable_pi_apply i).comp hXm).sub (hcut i)
    exact Measurable.ite hGt hbig measurable_const
end TruncPath

section Main

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

end Main

end LevyStochCalc.Ito.JumpFormula


