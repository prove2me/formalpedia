-- Prove2me | Definitions.Def_OrderedExperts_Supplement_FullInfoPolicy
-- name    : OrderedExperts_Supplement_FullInfoPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T06:34:16.063776+00:00
-- url     : https://prove2.me/theorems/9866c054-5a90-4d98-9f66-2cc6a099a6de
-- title:
--   General randomized full-information learner
-- statement:
--   A **full-information learner** chooses one current active rank from the preceding history. Only after that choice does the complete current loss vector on the experts' active recommendations enter its history.
--
--   **Formalization Note** The rule has no current-loss argument, which enforces the paper's timing. Repeated recommendations simply repeat one active loss coordinate.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Sec. 6, pp. 13–14

import Definitions.Def_OrderedExperts_chainSize

open Finset

namespace OrderedExperts.Supplement

/-- **A general randomized full-information learner.**
Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission
(held version), Sec. 6, pp. 13--14.

The learner selects a current active rank from the preceding history.  Only after that selection is
the current vector of losses at all expert recommendations appended to the history.

**Formalization Note.** The rule has no current-loss argument, so full information arrives after
the action as required.  Repeated recommendations merely repeat one active loss coordinate. -/
structure FullInfoPolicy (A : Type*) (n : ℕ) [LinearOrder A] where
  mass : (Fin n → A) → List ((Fin n → A) × ℕ × (Fin n → ℝ)) → ℕ → ℝ
  nonneg : ∀ current h, ∀ a ∈ Icc 1 (chainSize (fun _ ↦ current) 0),
    0 ≤ mass current h a
  total : ∀ current h,
    ∑ a ∈ Icc 1 (chainSize (fun _ ↦ current) 0), mass current h a = 1

end OrderedExperts.Supplement


