-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_SolvesAe_F000
-- name    : LevyStochCalc_BSDEJ_SolvesAe_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:44:11.506652+00:00
-- url     : https://prove2.me/theorems/13000ecf-309e-4f94-8215-fa0ca9ee8547
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.SolvesAe
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.SolvesAe. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_UniquenessIndistinguishable_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Solutions of a BSDEJ up to a null set of sample points

`SolvesBSDEJAe D f ξ T Y Z U` is the solution predicate `SolvesBSDEJ D f ξ T Y Z U` with its
three everywhere-quantified path conditions — right-continuity with left limits of `Y`, and the
vanishing of `Z` and of `U` off the horizon — asked only for almost every sample point.

The two predicates describe the same solutions: setting the three processes to `0` on a
measurable null superset of the exceptional set produces a `SolvesBSDEJ` triple whose paths agree
with the given ones off that null set (`SolvesBSDEJAe.exists_modification`), so the value
processes of two almost-everywhere solutions of the same equation remain indistinguishable on the
horizon.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

omit [IsProbabilityMeasure P] in
/-- An integrand vanishing off a horizon at almost every sample point, and having finite energy
on that horizon in each coordinate, is square integrable on every horizon. -/
theorem sq_int_global_of_vanishing_ae {Z : ℝ → Ω → (Fin d → ℝ)} {T : ℝ}
    (hvan : ∀ᵐ ω ∂P, ∀ s : ℝ, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
    (hsq : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤) :
    ∀ i : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  classical
  intro i T' _
  obtain ⟨g, hgz, hgeq⟩ : ∃ g : Ω → ℝ → ℝ, (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → g ω s = 0)
      ∧ ∀ᵐ ω ∂P, ∀ s : ℝ, g ω s = Z s ω i := by
    refine ⟨fun ω s => if (∀ s' : ℝ, s' ∉ Set.Icc (0 : ℝ) T → Z s' ω = 0) then Z s ω i else 0,
      ?_, ?_⟩
    · intro ω s hs
      dsimp only
      by_cases hc : ∀ s' : ℝ, s' ∉ Set.Icc (0 : ℝ) T → Z s' ω = 0
      · rw [if_pos hc, hc s hs]
        rfl
      · rw [if_neg hc]
    · filter_upwards [hvan] with ω hω
      intro s
      rw [if_pos hω]
  have hE : ∀ T'' : ℝ, LevyStochCalc.Brownian.Ito.energy P T'' g
      = LevyStochCalc.Brownian.Ito.energy P T'' fun ω s => Z s ω i := by
    intro T''
    refine lintegral_congr_ae ?_
    filter_upwards [hgeq] with ω hω
    exact lintegral_congr fun s => by rw [hω s]
  have hle := _root_.Prove2MeSourceProof.h_6afbd3f9a4aa317ea9c9ba3c (P := P) hgz T'
  rw [hE T', hE T] at hle
  exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr (hsq i))
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A marked integrand vanishing off a horizon at almost every sample point, and having finite
marked energy on that horizon, is square integrable on every horizon. -/
theorem marked_sq_int_global_of_vanishing_ae {U : ℝ → Ω → E → ℝ} {T : ℝ}
    (hvan : ∀ᵐ ω ∂P, ∀ (s : ℝ) (e : E), s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0)
    (hsq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖(fun ω' s e => U s ω' e) ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  classical
  intro T' _
  obtain ⟨g, hgz, hgeq⟩ : ∃ g : Ω → ℝ → E → ℝ,
      (∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → g ω s e = 0)
      ∧ ∀ᵐ ω ∂P, ∀ (s : ℝ) (e : E), g ω s e = U s ω e := by
    refine ⟨fun ω s e =>
      if (∀ (s' : ℝ) (e' : E), s' ∉ Set.Icc (0 : ℝ) T → U s' ω e' = 0) then U s ω e else 0,
      ?_, ?_⟩
    · intro ω s e hs
      dsimp only
      by_cases hc : ∀ (s' : ℝ) (e' : E), s' ∉ Set.Icc (0 : ℝ) T → U s' ω e' = 0
      · rw [if_pos hc, hc s e hs]
      · rw [if_neg hc]
    · filter_upwards [hvan] with ω hω
      intro s e
      rw [if_pos hω]
  have hE : ∀ T'' : ℝ, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T'' g
      = LevyStochCalc.Poisson.Compensated.markedEnergy P ν T'' fun ω s e => U s ω e := by
    intro T''
    refine lintegral_congr_ae ?_
    filter_upwards [hgeq] with ω hω
    exact lintegral_congr fun s => lintegral_congr fun e => by rw [hω s e]
  have hle := _root_.Prove2MeSourceProof.h_5fad5a5e72ace6c4e33f3a33
    (P := P) (ν := ν) hgz T'
  rw [hE T', hE T] at hle
  exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hsq)
/-- `(Y, Z, U)` solves the BSDEJ with generator `f`, terminal value `ξ` and horizon `T`, driven
by `D` over the augmented joint filtration `augJoint D`, with the path conditions on `Y`, `Z` and
`U` holding for almost every sample point:

`Y_t = ξ + ∫_t^T f(s, Y_s, Z_s, U_s) ds − ∫_t^T Z_s dW_s − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`

almost surely at each `t ∈ [0, T]`, with the two stochastic integrals the canonical ones for
`augJoint D`, `Y` almost surely càdlàg, adapted to `(augJoint D).rightCont` and of finite `S²`
seminorm on the horizon, and `Z`, `U` progressive with finite energy on `[0, T]` and almost surely
vanishing off it. -/
structure SolvesBSDEJAe (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ) (ξ : Ω → ℝ) (T : ℝ)
    (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) : Prop where
  /-- Each coordinate of `Z` is jointly measurable. -/
  Z_meas : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i)
  /-- Each coordinate of `Z` is progressively measurable for the augmented joint filtration. -/
  Z_prog : ∀ i : Fin d,
    LevyStochCalc.Probability.ProgressivelyMeasurable (augJoint D) fun ω s => Z s ω i
  /-- `Z` vanishes off the horizon at almost every sample point. -/
  Z_vanish : ∀ᵐ ω ∂P, ∀ s : ℝ, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0
  /-- Each coordinate of `Z` has finite energy on the horizon. -/
  Z_sq : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤
  /-- `U` is jointly measurable in the sample point, the time and the mark. -/
  U_meas : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2
  /-- `U` is marked progressively measurable for the augmented joint filtration. -/
  U_prog : LevyStochCalc.Probability.MarkedProgressivelyMeasurable (augJoint D)
    fun ω s e => U s ω e
  /-- `U` vanishes off the horizon at almost every sample point. -/
  U_vanish : ∀ᵐ ω ∂P, ∀ (s : ℝ) (e : E), s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0
  /-- `U` has finite marked energy on the horizon. -/
  U_sq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤
  /-- `Y` is jointly measurable. -/
  Y_meas : Measurable (Function.uncurry Y)
  /-- `Y` is adapted to the right-continuous augmented joint filtration. -/
  Y_adapted : MeasureTheory.Adapted (augJoint D).rightCont Y
  /-- Almost every path of `Y` is right-continuous with left limits. -/
  Y_cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ,
    Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
      ∧ ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L)
  /-- The running supremum of `Y` on the horizon is square integrable. -/
  Y_sup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤
  /-- The backward equation, almost surely at each time of the horizon. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
    Y t ω = ξ ω + (∫ s in Set.Icc t T, f s (Y s ω) (Z s ω) (U s ω))
      - (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
            (augJoint D) D.isBrownianFiltration_aug Z Z_meas Z_prog
            (sq_int_global_of_vanishing_ae Z_vanish Z_sq) T ω
          - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
            (augJoint D) D.isBrownianFiltration_aug Z Z_meas Z_prog
            (sq_int_global_of_vanishing_ae Z_vanish Z_sq) t ω)
      - (LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N (augJoint D)
            D.isPoissonFiltration_aug (fun ω' s e => U s ω' e) U_meas U_prog
            (marked_sq_int_global_of_vanishing_ae U_vanish U_sq) T ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N (augJoint D)
            D.isPoissonFiltration_aug (fun ω' s e => U s ω' e) U_meas U_prog
            (marked_sq_int_global_of_vanishing_ae U_vanish U_sq) t ω)
/-- A solution is a solution up to a null set of sample points. -/
theorem SolvesBSDEJ.toAe {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : SolvesBSDEJ D f ξ T Y Z U) :
    SolvesBSDEJAe D f ξ T Y Z U where
  Z_meas := h.Z_meas
  Z_prog := h.Z_prog
  Z_vanish := Filter.Eventually.of_forall fun ω => h.Z_vanish ω
  Z_sq := h.Z_sq
  U_meas := h.U_meas
  U_prog := h.U_prog
  U_vanish := Filter.Eventually.of_forall fun ω => h.U_vanish ω
  U_sq := h.U_sq
  Y_meas := h.Y_meas
  Y_adapted := h.Y_adapted
  Y_cadlag := Filter.Eventually.of_forall fun ω => h.Y_cadlag ω
  Y_sup := h.Y_sup
  eqn := h.eqn
end LevyStochCalc.BSDEJ.Solves


