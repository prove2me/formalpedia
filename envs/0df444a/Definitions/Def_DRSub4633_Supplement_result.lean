-- Prove2me | Definitions.Def_DRSub4633_Supplement_result
-- name    : DRSub4633_Supplement_result
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:28:33.010477+00:00
-- url     : https://prove2.me/theorems/dc168055-4d13-49fc-9e48-5a0352da8a86
-- title:
--   The output of a run
-- statement:
--   For an algorithm $A$, oracles $O$ and a seed $\omega$, the output is the point $y$ that $A$ returns at the first step at which it stops. Since the transcript no longer changes after that step, the output is the same at every later step.
--
--   **Formalization Note** If the run never stops, the value is $0$. This junk value plays no role in Theorem 6.3, which asserts that every run stops.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Theorem 6.3, p.37

import Mathlib
import Definitions.Def_DRSub4633_Supplement_transcript

namespace DRSub4633.Supplement

/-- **The output of a run.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Theorem 6.3, p.37: "a randomized algorithm returning `y`".

`result A O ω` is the point output by the strategy `A` with seed `ω` against the oracles `O`, at
the first step `k` at which `A` outputs (the output is the same at every later step, since the
transcript no longer changes).

**Formalization Note.** If the run never outputs, the value is `0` (a junk value); Theorem 6.3
asserts termination of every run separately, so this case does not occur there. -/
noncomputable def result {n : ℕ} {Ω : Type} (A : Strategy n Ω) (O : Oracles n) (ω : Ω) :
    EuclideanSpace ℝ (Fin n) := by
  classical
  exact if h : ∃ k, ∃ y, A ω (transcript A O ω k) = Sum.inr y then
    (match A ω (transcript A O ω (Nat.find h)) with
      | Sum.inr y => y
      | Sum.inl _ => 0)
  else 0

end DRSub4633.Supplement


