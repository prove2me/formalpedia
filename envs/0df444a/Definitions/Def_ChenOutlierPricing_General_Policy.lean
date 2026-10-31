-- Prove2me | Definitions.Def_ChenOutlierPricing_General_Policy
-- name    : ChenOutlierPricing_General_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:40:56.620129+00:00
-- url     : https://prove2.me/theorems/45ff2075-8886-4fa0-9b0d-7ae27b324768
-- title:
--   Observed-history randomized policies and private random tapes
-- statement:
--   Defines a general measurable, feasible randomized policy from a public horizon, real initial stock, private random tape, and finite price/sales history to a price in a nonnegative compact real interval. The uniform tape has independent Uniform[0,1] coordinates. A policy has no demand curve, contamination budget, clearance price, optimum price, or regime input. The public interval is not normalized to [0,1].
-- source:
--   Chen and Wang, DOI 10.1287/opre.2022.2280, §3.1, supplied source.pdf p. 11

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ChenOutlierPricing.General

/-- Private random tape and the seller's observed history, in elapsed-time order. -/
abbrev Tape := ℕ → ℝ
abbrev Observation := ℝ × ℝ
abbrev History := List Observation

/-- A randomized policy receives only public horizon, initial stock, its own tape,
and observed price/sales history. No demand curve or corruption budget is an input. -/
abbrev Policy := ℕ → ℝ → Tape → History → ℝ

/-- Public feasible price interval. -/
structure PriceBand where
  lo : ℝ
  hi : ℝ
  nonneg : 0 ≤ lo
  ordered : lo < hi

/-- Feasible, measurable operational policy. The private seed may be retained across rounds. -/
def PolicyAdmissible (B : PriceBand) (π : Policy) : Prop :=
  (∀ T x u h, π T x u h ∈ Set.Icc B.lo B.hi) ∧
  (∀ T x n, Measurable (fun v : Tape × (Fin n → Observation) =>
    π T x v.1 (List.ofFn v.2)))

/-- Independent uniform coordinates for private randomization. -/
def UniformTape {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (U : Ω → Tape) : Prop :=
  Measurable U ∧ iIndepFun (fun i ω => U ω i) μ ∧
    ∀ i, Measure.map (fun ω => U ω i) μ = volume.restrict (Set.Icc (0 : ℝ) 1)

end ChenOutlierPricing.General


