-- Prove2me | Definitions.Def_OrderedExperts_Supplement_oneExpLoss
-- name    : OrderedExperts_Supplement_oneExpLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T06:32:39.558329+00:00
-- url     : https://prove2.me/theorems/9e6478e0-d02d-4409-8de7-cd4688f42e4b
-- title:
--   Exact expected paid loss under one-point feedback
-- statement:
--   The exact expected cumulative loss of a one-point learner is the finite recursion that charges the loss at the one queried active recommendation, appends the observation returned at that point, and continues with the learner's next conditional action law.
--
--   This quantity is compared with the best expert's cumulative loss in the one-point regret theorems.
--
--   **Formalization Note** The recursion sums over all adaptive learner randomization exactly; rounds are 0-based.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Sec. 6, p. 13

import Definitions.Def_OrderedExperts_Supplement_OnePointPolicy
import Definitions.Def_OrderedExperts_chainPt

open Finset

namespace OrderedExperts.Supplement

/-- **Exact expected paid loss of a one-point learner.**
Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission
(held version), Sec. 6, p. 13.

The learner pays the loss at its one queried active rank, receives `observe t a`, and continues
from the resulting history.

**Formalization Note.** This finite recursion is the exact expectation over all adaptive learner
randomness; rounds are zero-based. -/
noncomputable def oneExpLoss {A : Type*} [LinearOrder A] [OrderBot A] {n : ℕ} {O : Type*}
    (P : OnePointPolicy A n O) (rec : ℕ → Fin n → A) (loss : ℕ → A → ℝ)
    (observe : ℕ → ℕ → O) :
    ℕ → ℕ → List ((Fin n → A) × ℕ × O) → ℝ
  | 0, _, _ => 0
  | k + 1, t, h =>
      ∑ a ∈ Icc 1 (chainSize rec t), P.mass (rec t) h a *
        (loss t (chainPt rec t a) +
          oneExpLoss P rec loss observe k (t + 1) (h ++ [(rec t, a, observe t a)]))

end OrderedExperts.Supplement


