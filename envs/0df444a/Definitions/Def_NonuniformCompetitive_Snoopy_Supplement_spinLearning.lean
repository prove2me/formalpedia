-- Prove2me | Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_spinLearning
-- name    : NonuniformCompetitive_Snoopy_Supplement_spinLearning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:54:26.413942+00:00
-- url     : https://prove2.me/theorems/2afef61e-c8f7-4eb7-a69e-16264a073fa8
-- title:
--   Measurable causal spin policies and competitiveness under arbitrary iid laws
-- statement:
--   A deterministic spin policy chooses a threshold from the completed lock-wait history. Its evaluation is measurable on every finite history space; an infinite threshold represents never blocking. For a probability law $P$ on all nonnegative real waiting times, distributional competitiveness is
--   $$\exists a\in\mathbb R\ \forall N\in\mathbb N:\quad
--   \mathbf E_{P^N} C_A\le c\,\mathbf E_{P^N} C_{opt}+a.$$
--   The cost functions are the published spin-block functions, with $C_{opt}=\sum\min\{\tau,C\}$ and release priority at a threshold tie. Expectations are lower integrals of nonnegative measurable costs, rather than Bochner integrals that default to zero when not integrable.
--
--   This defines the full measurable policy space and the finite-horizon iid comparison. It places no density, moment, bounded-support or atom exclusions on $P$.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, §4.1, pp. 558–561, especially Theorem 11

import Mathlib
import Definitions.Def_NonuniformCompetitive_SpinBlock_Model

namespace NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory
open scoped NNReal ENNReal

/-- A regular deterministic causal threshold policy. Measurability is required
on each finite history space, not merely on fixed input sequences. Thresholds
may be infinite (never block), so the policy space contains ordinary algorithms. -/
structure SpinLearner where
  policy : NonuniformCompetitive.SpinBlock.OnlineAlg
  regular : ∀ m : ℕ, Measurable fun h : Fin m → ℝ≥0 => policy.blockTime (List.ofFn h)

/-- Distributional competitiveness under EVERY finite iid horizon, without
moment, density, support or atom restrictions on the probability measure P. -/
def SpinIIDCompetitive (C : ℝ) (A : SpinLearner) (P : Measure ℝ≥0) (c : ℝ) : Prop :=
  ∃ a : ℝ, ∀ N : ℕ,
    (∫⁻ x : Fin N → ℝ≥0, A.policy.cost C (List.ofFn x) ∂Measure.pi (fun _ => P)) ≤
      ENNReal.ofReal c *
        (∫⁻ x : Fin N → ℝ≥0,
          ENNReal.ofReal (NonuniformCompetitive.SpinBlock.optCost C (List.ofFn x))
          ∂Measure.pi (fun _ => P)) + ENNReal.ofReal a

end NonuniformCompetitive.Snoopy.Supplement


