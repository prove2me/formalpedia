-- Prove2me | Definitions.Def_OrderedExperts_Supplement_twoExpLoss
-- name    : OrderedExperts_Supplement_twoExpLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T06:27:41.025646+00:00
-- url     : https://prove2.me/theorems/25820d68-e2d4-4052-953e-0b6ca4128a9d
-- title:
--   Exact expected paid loss under two-point feedback
-- statement:
--   For a randomized two-point learner, an oblivious recommendation sequence, an oblivious loss sequence, and a protocol-specific observation rule, the expected cumulative paid loss is defined recursively. On each round the learner pays the average of the losses at its two queried active recommendations, receives only the prescribed observation, and continues from the enlarged history.
--
--   This gives the expectation used in all two-point upper and lower bounds.
--
--   **Formalization Note** Rounds are 0-based. Every expectation is an exact finite sum over conditional pair laws, so there is no measurability, integrability, or default-value case.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Sec. 2.2, pp. 5–6

import Definitions.Def_OrderedExperts_Supplement_TwoPointPolicy
import Definitions.Def_OrderedExperts_chainPt

open Finset

namespace OrderedExperts.Supplement

/-- **Exact expected paid loss of a two-point learner.**
Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission
(held version), Sec. 2.2, pp. 5--6.

The learner pays the average loss of the two queried active recommendations.  The recursion sums
over the learner's conditional pair law and appends only the observation supplied by the feedback
protocol.

**Formalization Note.** Rounds are zero-based.  Since each conditional law is finite, this is the
expectation exactly and has no integrability or measurability default case. -/
noncomputable def twoExpLoss {A : Type*} [LinearOrder A] [OrderBot A] {n : ℕ} {O : Type*}
    (P : TwoPointPolicy A n O) (rec : ℕ → Fin n → A) (loss : ℕ → A → ℝ)
    (observe : ℕ → ℕ → ℕ → O) :
    ℕ → ℕ → List ((Fin n → A) × ℕ × ℕ × O) → ℝ
  | 0, _, _ => 0
  | k + 1, t, h =>
      ∑ a ∈ Icc 1 (chainSize rec t), ∑ b ∈ Icc 1 (chainSize rec t),
        P.mass (rec t) h a b *
          ((loss t (chainPt rec t a) + loss t (chainPt rec t b)) / 2 +
            twoExpLoss P rec loss observe k (t + 1)
              (h ++ [(rec t, a, b, observe t a b)]))

end OrderedExperts.Supplement


