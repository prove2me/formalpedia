-- Prove2me | Definitions.Def_TIESharp_IsFeasible
-- name    : TIESharp_IsFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:02.586959+00:00
-- url     : https://prove2.me/theorems/aee42fe4-6021-4e19-bc60-e6746f7605c3
-- title:
--   Feasible family: $y^m(b)$ is a probability distribution over assignments
-- statement:
--   A family is **feasible** if, at every job count $m$ and every nonnegative bid profile $b$, its allocation weights form a probability distribution over assignments:
--   $$y^m_A(b)\ge0\quad(A\in\mathcal A_{m,n}),\qquad \sum_{A\in\mathcal A_{m,n}}y^m_A(b)=1.$$
--
--   **Formalization Note.** Only nonnegative bids are constrained; values at profiles with a negative entry are irrelevant.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §2, p.3

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_Family

set_option autoImplicit false

namespace TIESharp

/-- A family is **feasible** if at every job count `m` and every nonnegative bid profile `b` its
allocation rule specifies a distribution `y^m(b) = (y^m_A(b))_{A ∈ A_{m,n}}` over assignments
(Li, *Sharp Bounds for Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §2, p.3): all weights
are nonnegative and they sum to one.

**Formalization Note.** Only nonnegative bids are constrained, as the bid space is
`[0, ∞)^{n×m}`; values at profiles with a negative entry are irrelevant. -/
def IsFeasible {n : ℕ} (F : Family n) : Prop :=
  ∀ (m : ℕ) (b : Fin n → Fin m → ℝ), Nonneg b →
    (∀ A, 0 ≤ F.alloc m b A) ∧ ∑ A, F.alloc m b A = 1

end TIESharp


