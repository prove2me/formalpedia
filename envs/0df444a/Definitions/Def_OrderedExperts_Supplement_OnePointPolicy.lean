-- Prove2me | Definitions.Def_OrderedExperts_Supplement_OnePointPolicy
-- name    : OrderedExperts_Supplement_OnePointPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T06:30:01.503234+00:00
-- url     : https://prove2.me/theorems/55fb135f-8739-4068-bea9-2eb29d60f9ae
-- title:
--   General randomized one-point learner
-- statement:
--   A **randomized one-point learner** receives the current recommendations and its previous one-point feedback history, then chooses one current active rank according to a probability mass function. It subsequently receives only the problem-specific observation at the chosen point.
--
--   **Formalization Note** Conditional finite laws represent arbitrary randomized nonanticipating play, and the rule cannot inspect the current loss before choosing.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Sec. 6, p. 13

import Definitions.Def_OrderedExperts_chainSize

open Finset

namespace OrderedExperts.Supplement

/-- **A general randomized one-point learner.**
Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission
(held version), Sec. 6, p. 13.

At each history the learner gives a probability mass function on the current active ranks; after
playing a rank it receives only the protocol-specific observation `O` at that point.

**Formalization Note.** The conditional finite-law representation is equivalent to arbitrary
randomized nonanticipating play and exposes no current loss to the rule. -/
structure OnePointPolicy (A : Type*) (n : ℕ) (O : Type*) [LinearOrder A] where
  mass : (Fin n → A) → List ((Fin n → A) × ℕ × O) → ℕ → ℝ
  nonneg : ∀ current h, ∀ a ∈ Icc 1 (chainSize (fun _ ↦ current) 0),
    0 ≤ mass current h a
  total : ∀ current h,
    ∑ a ∈ Icc 1 (chainSize (fun _ ↦ current) 0), mass current h a = 1

end OrderedExperts.Supplement


