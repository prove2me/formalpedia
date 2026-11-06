-- Prove2me | Definitions.Def_TIESharp_IsBSSlotLaw
-- name    : TIESharp_IsBSSlotLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:07.131362+00:00
-- url     : https://prove2.me/theorems/bf401c55-9eb1-4e91-be50-6375f9431928
-- title:
--   Slot-rounding law of the Bounded-Square probabilities
-- statement:
--   A function $y$ on assignments is a **slot-rounding law** of the Bounded-Square probabilities at profile $t$ if it is a probability distribution over assignments,
--   $$y_A\ge0,\qquad\sum_A y_A=1,\qquad \sum_{A:\,A(j)=i}y_A=q_{ij}(t)\ \text{ for all } i,j,$$
--   supported on slot-feasible assignments. The mechanism of Theorem 3.3 draws one perfect matching from a decomposition of the slot matrix; its law is of this kind, and the paper's load bounds "hold for every such decomposition".
--
--   **Formalization Note.** Statements quantify over every such law, which contains every Hall/Birkhoff decomposition of Sec. 5.2.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §3.2, p.10; §5.2, p.23

import Mathlib
import Definitions.Def_TIESharp_bsProb
import Definitions.Def_TIESharp_SlotFeasible

set_option autoImplicit false

namespace TIESharp

/-- `y` is a **slot-rounding law of the Bounded-Square probabilities** at profile `t` (Li, *Sharp
Bounds for Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §3.2, p.10, and §5.2, p.23): a
probability distribution over assignments whose marginals are the Bounded-Square probabilities,
`P(A(j) = i) = q_ij(t)`, and which is supported on slot-feasible assignments.

**Formalization Note.** The paper draws a matching from a decomposition of the slot matrix chosen
by a fixed augmenting-path rule and notes "The load bounds below hold for every such
decomposition" (p.23). This predicate admits every such law: it contains every Hall/Birkhoff
decomposition, so statements about all `y` with `IsBSSlotLaw t y` cover the paper's mechanism. -/
def IsBSSlotLaw {n m : ℕ} (t : Fin n → Fin m → ℝ) (y : (Fin m → Fin n) → ℝ) : Prop :=
  (∀ A, 0 ≤ y A) ∧ ∑ A, y A = 1 ∧
    (∀ i j, ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i), y A = bsProb t i j) ∧
    (∀ A, 0 < y A → SlotFeasible t A)

end TIESharp


