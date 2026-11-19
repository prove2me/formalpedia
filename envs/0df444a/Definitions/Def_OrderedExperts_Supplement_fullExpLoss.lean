-- Prove2me | Definitions.Def_OrderedExperts_Supplement_fullExpLoss
-- name    : OrderedExperts_Supplement_fullExpLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T06:35:54.744192+00:00
-- url     : https://prove2.me/theorems/d12a71b5-b58a-4805-a7b5-abdcfb5d7694
-- title:
--   Exact expected paid loss under full information
-- statement:
--   The expected cumulative paid loss under full information is defined by first sampling the learner's current active rank, charging the loss at that recommendation, and only then appending the full current expert-loss vector to the history.
--
--   **Formalization Note** This is an exact finite expectation. The current vector is unavailable at the action-selection step and becomes available only to future rounds.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Sec. 6, pp. 13–14

import Definitions.Def_OrderedExperts_Supplement_FullInfoPolicy
import Definitions.Def_OrderedExperts_chainPt

open Finset

namespace OrderedExperts.Supplement

/-- **Exact expected paid loss under full information.**
Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission
(held version), Sec. 6, pp. 13--14.

After the learner chooses and pays for one active recommendation, the complete current expert-loss
vector is appended to the history.

**Formalization Note.** This is an exact finite expectation.  The current loss vector is absent
from the policy call and appears only in the recursive history, encoding the paper's timing. -/
noncomputable def fullExpLoss {A : Type*} [LinearOrder A] [OrderBot A] {n : ℕ}
    (P : FullInfoPolicy A n) (rec : ℕ → Fin n → A) (loss : ℕ → A → ℝ) :
    ℕ → ℕ → List ((Fin n → A) × ℕ × (Fin n → ℝ)) → ℝ
  | 0, _, _ => 0
  | k + 1, t, h =>
      ∑ a ∈ Icc 1 (chainSize rec t), P.mass (rec t) h a *
        (loss t (chainPt rec t a) +
          fullExpLoss P rec loss k (t + 1)
            (h ++ [(rec t, a, fun f ↦ loss t (rec t f))]))

end OrderedExperts.Supplement


