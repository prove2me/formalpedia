-- Prove2me | Definitions.Def_OrderedExperts_Supplement_TwoPointPolicy
-- name    : OrderedExperts_Supplement_TwoPointPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T06:24:42.950762+00:00
-- url     : https://prove2.me/theorems/a53a94c3-a520-4f64-8b07-3127af83e010
-- title:
--   General randomized two-point learner
-- statement:
--   A **randomized two-point learner** receives the current recommendations and its complete preceding feedback history, then chooses an ordered pair of current active ranks according to a probability mass function. A history entry records the recommendations, the two queried ranks, and exactly the observation returned by the chosen feedback protocol.
--
--   This object is reusable for both separated-monotone feedback, where both components are observed at each query, and BV feedback, where only the two aggregate losses are observed.
--
--   **Formalization Note** Randomness is represented by a conditional finite law at every history. This is equivalent to a randomized nonanticipating policy because every active chain is finite, and the rule has no current-loss argument.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Sec. 2.2, pp. 5–6

import Definitions.Def_OrderedExperts_chainSize

open Finset

namespace OrderedExperts.Supplement

/-- **A general randomized two-point learner.**
Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission
(held version), Sec. 2.2, pp. 5--6.

Given the current recommendations and the complete preceding feedback history, `mass` is a
probability mass function on the ordered pairs of current active ranks.  A history entry records
the recommendations, the two ranks queried, and exactly the protocol-specific observation `O`.

**Formalization Note.** Randomization is represented by its conditional finite law at every
history.  This is equivalent to a randomized nonanticipating policy because every round has a
finite active chain.  The policy has no argument for the current loss and hence cannot anticipate
it. -/
structure TwoPointPolicy (A : Type*) (n : ℕ) (O : Type*) [LinearOrder A] where
  mass : (Fin n → A) → List ((Fin n → A) × ℕ × ℕ × O) → ℕ → ℕ → ℝ
  nonneg : ∀ current h, ∀ a ∈ Icc 1 (chainSize (fun _ ↦ current) 0),
    ∀ b ∈ Icc 1 (chainSize (fun _ ↦ current) 0), 0 ≤ mass current h a b
  total : ∀ current h,
    ∑ a ∈ Icc 1 (chainSize (fun _ ↦ current) 0),
      ∑ b ∈ Icc 1 (chainSize (fun _ ↦ current) 0), mass current h a b = 1

end OrderedExperts.Supplement


