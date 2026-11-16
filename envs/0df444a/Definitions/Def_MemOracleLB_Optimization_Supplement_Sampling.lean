-- Prove2me | Definitions.Def_MemOracleLB_Optimization_Supplement_Sampling
-- name    : MemOracleLB_Optimization_Supplement_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:12:04.239768+00:00
-- url     : https://prove2.me/theorems/f11545ae-fcf3-4019-bb00-a5dc2240277d
-- title:
--   Adaptive point-valued sampling and its output law
-- statement:
--   An adaptive membership sampler in Euclidean dimension $n$ chooses its next query or final point from the finite Boolean answer history and its internal random seed $\omega$. At each fixed history the action is measurable in the seed. The sampler has no access to the body except through exact membership answers, with boundary points included.
--
--   The run starts with the empty history, appends one Boolean answer per query, and ceases to have a history after it halts. Its query count $T$ is the number of answered queries before halting, with $T=+\infty$ on an infinite run. For each finite history, restrict the seed measure to the seeds that halt at precisely that history and push it forward by the point output. Summing over these disjoint halting leaves defines the output sub-probability law; non-halting seeds contribute no mass and are never renormalized away. The point-output map is measurably extended by zero on query actions, with its measurability proved in this module.
--
--   For a body $K$, its uniform law is normalized Lebesgue measure,
--   $$U_K=(\operatorname{vol}K)^{-1}\operatorname{vol}|_K.$$
--   The published class predicate guarantees positive finite volume. These definitions supply the point-valued interface needed for the sampling lower bound; the existing real-valued optimizer interface remains unchanged.
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Theorem 1.2, PDF p. 3 (printed p. 2), oracle setting PDF p. 2 (printed p. 1), sampling proof PDF p. 21 (printed p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_OracleModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace MemOracleLB.Optimization.Supplement

/-- An adaptive point-valued sampler. Only the seed dependence at each history is measurable;
the body is available solely through the membership oracle (PDF p.3, Theorem 1.2). -/
structure SamplingAlgorithm (n : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  action : List Bool → Ω → Sum (E n) (E n)
  measurable_seed : ∀ h, Measurable (action h)

/-- Finite histories; a run that has halted has no later history. -/
def samplingRunHistory {n : ℕ} (action : List Bool → Sum (E n) (E n))
    (O : E n → Bool) : ℕ → Option (List Bool)
  | 0 => some []
  | k + 1 => do
      let h ← samplingRunHistory action O k
      match action h with
      | .inl q => some (h ++ [O q])
      | .inr _ => none

/-- Queries before halting; the empty infimum in ENat is infinity. -/
def samplingQueryCount {n : ℕ} (action : List Bool → Sum (E n) (E n))
    (O : E n → Bool) : ℕ∞ :=
  sInf {k | ∃ (t : ℕ) (h : List Bool) (z : E n), k = (t : ℕ∞) ∧
    samplingRunHistory action O t = some h ∧ action h = Sum.inr z}

def samplingQueries {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : SamplingAlgorithm n Ω) (K : Set (E n)) (ω : Ω) : ℕ∞ :=
  samplingQueryCount (fun h => S.action h ω) (membershipOracle K)

/-- A total extension of the point output at a fixed history, equal to zero on query actions.
Only its values on haltSeeds are used. -/
def pointOutput {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : SamplingAlgorithm n Ω) (h : List Bool) (ω : Ω) : E n :=
  Sum.elim (fun _ => 0) id (S.action h ω)

/-- Structural measurability: the pushforwards below never use a nonmeasurable map. -/
theorem measurable_pointOutput {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : SamplingAlgorithm n Ω) (h : List Bool) : Measurable (pointOutput S h) :=
  (measurable_const.sumElim measurable_id).comp (S.measurable_seed h)

/-- Seeds halting exactly at the leaf h. For Borel K these are measurable, disjoint events. -/
def haltSeeds {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : SamplingAlgorithm n Ω) (K : Set (E n)) (h : List Bool) : Set Ω :=
  {ω | samplingRunHistory (fun g => S.action g ω) (membershipOracle K) h.length = some h ∧
    (S.action h ω).isRight}

/-- Output sub-probability law: sum the measurable point-output pushforward on each halting
leaf. Nonhalting seeds contribute no mass; no conditioning on termination is performed. -/
def outputLaw {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : SamplingAlgorithm n Ω) (K : Set (E n)) (P : Measure Ω) : Measure (E n) :=
  Measure.sum (fun h : List Bool =>
    (P.restrict (haltSeeds S K h)).map (pointOutput S h))

/-- Normalized Lebesgue measure on K. InClass guarantees positive finite volume. -/
def uniformLaw {n : ℕ} (K : Set (E n)) : Measure (E n) :=
  ProbabilityTheory.cond volume K

end MemOracleLB.Optimization.Supplement


