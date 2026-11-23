-- Prove2me | Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_adaptiveSpin
-- name    : NonuniformCompetitive_Snoopy_Supplement_adaptiveSpin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:54:05.07089+00:00
-- url     : https://prove2.me/theorems/8b903088-06ce-4c05-b983-37d60182fc92
-- title:
--   Causal positive-delay lock-release tests and their online competitors
-- statement:
--   A completed lock wait reveals its release time and any blocking event that actually occurred before release. If the lock was released while the process still spun, the latent future blocking time is not revealed. A delayed-release test chooses a finite timeout from completed observations; after observing a block it chooses a strictly positive release delay, capped by that timeout.
--
--   Uniform comparison on this subclass requires
--   $$\mathbf E C_A(\sigma(S))\le c\,\mathbf E C_B(\sigma(S))+a$$
--   with one $a$ for every bounded wait count, causal release test and causal online comparator with measurable interacting costs and finite expected comparison cost. Every algorithm competitive against all adaptive online adversaries satisfies this test predicate.
--
--   Threshold evaluation is jointly measurable in the coins and each finite history, without any finite-mean blocking-time condition. The imported wait cost gives release priority at exact equality. Positive delays preserve that convention while testing the lower bound.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, §1, p. 543; §4.1, Theorem 9 and proof, p. 559

import Mathlib
import Definitions.Def_NonuniformCompetitive_SpinBlock_Randomized

namespace NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory
open scoped NNReal ENNReal

/-- Completed waits reveal release time and the block event if it occurred.
An unobserved latent future time to block is recorded as ∞, never revealed. -/
abbrev SpinTranscript := List (ℝ≥0 × ℝ≥0∞)

/-- A useful SUBCLASS of adaptive online adversaries: set a finite timeout;
after observing blocking, release after a strictly positive delay, unless the
timeout occurs first. Count truncation is uniform in the random bits. -/
structure SpinDelayedStrategy where
  timeout : SpinTranscript → ℝ≥0
  delay : SpinTranscript → ℝ≥0 → ℝ≥0
  positive : ∀ h b, 0 < delay h b

noncomputable def SpinDelayedStrategy.release (S : SpinDelayedStrategy)
    (h : SpinTranscript) (b : ℝ≥0∞) : ℝ≥0 :=
  if b < (S.timeout h : ℝ≥0∞) then
    min (S.timeout h) (b.toNNReal + S.delay h b.toNNReal)
  else S.timeout h

noncomputable def spinPlay (A : NonuniformCompetitive.SpinBlock.OnlineAlg)
    (S : SpinDelayedStrategy) : ℕ → SpinTranscript
  | 0 => []
  | N + 1 =>
      let h := spinPlay A S N
      let b := A.blockTime (h.map Prod.fst)
      let τ := S.release h b
      h ++ [(τ, if b < (τ : ℝ≥0∞) then b else ⊤)]

noncomputable def spinInput (A : NonuniformCompetitive.SpinBlock.OnlineAlg)
    (S : SpinDelayedStrategy) (N : ℕ) : List ℝ≥0 :=
  (spinPlay A S N).map Prod.fst

/-- Jointly measurable evaluation at each finite random history. In particular
this licenses the adaptive experiment, which fixed-word cost measurability
alone does not. There is no assumption on expected blocking time. -/
def SpinRegular {C : ℝ} (A : NonuniformCompetitive.SpinBlock.RandomizedAlg C) : Prop :=
  ∀ m : ℕ, Measurable fun z : A.ι × (Fin m → ℝ≥0) =>
    (A.alg z.1).blockTime (List.ofFn z.2)

noncomputable def spinInteractingCost {C : ℝ}
    (A : NonuniformCompetitive.SpinBlock.RandomizedAlg C) (S : SpinDelayedStrategy)
    (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ i, (A.alg i).cost C (spinInput (A.alg i) S N) ∂A.μ

noncomputable def spinComparatorCost {C : ℝ}
    (A : NonuniformCompetitive.SpinBlock.RandomizedAlg C) (S : SpinDelayedStrategy)
    (N : ℕ) (B : NonuniformCompetitive.SpinBlock.OnlineAlg) : ℝ≥0∞ :=
  ∫⁻ i, B.cost C (spinInput (A.alg i) S N) ∂A.μ

/-- Uniform competitiveness even just on the delayed-release test class. Every
algorithm competitive against ALL adaptive online adversaries satisfies this
predicate. B is causal on the same generated waits and does not see A's coins. -/
def SpinDelayedTestCompetitive {C : ℝ}
    (A : NonuniformCompetitive.SpinBlock.RandomizedAlg C) (c : ℝ) : Prop :=
  ∃ a : ℝ, ∀ (N : ℕ) (S : SpinDelayedStrategy) (B : NonuniformCompetitive.SpinBlock.OnlineAlg),
    Measurable (fun i => (A.alg i).cost C (spinInput (A.alg i) S N)) →
    Measurable (fun i => B.cost C (spinInput (A.alg i) S N)) →
    spinComparatorCost A S N B ≠ ⊤ →
    spinInteractingCost A S N ≤ ENNReal.ofReal (c * (spinComparatorCost A S N B).toReal + a)

end NonuniformCompetitive.Snoopy.Supplement


