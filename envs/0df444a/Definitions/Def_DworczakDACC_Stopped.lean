-- Prove2me | Definitions.Def_DworczakDACC_Stopped
-- name    : DworczakDACC_Stopped
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:23.081356+00:00
-- url     : https://prove2.me/theorems/5f65b005-29a7-4721-ae55-51884a5c9e1b
-- title:
--   Stopping criterion of DACC: every agent holds the best option of its budget set
-- statement:
--   A state satisfies the **stopping criterion** when every agent weakly prefers its current partner to the best option of its budget set:
--
--   $$\mu(i)\ \succeq^i\ \arg\max\{B_i\cup\{\emptyset\};\succ^i\}\qquad\text{for all } i\in N .$$
--
--   This is the negation of the guard of the main loop of Algorithm 1 ("While $\exists i\in N$, $\mu(i)\prec^i\arg\max\{B_i;\succ^i\}$"): the algorithm stops at the first time this holds.
--
--   **Formalization Note** "Weakly prefers" is $\le$ on ranks. A decidability instance is provided so that the algorithm can test the criterion.
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Algorithm 1, main block, line 4, p. 8; §3, p. 7

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_State
import Definitions.Def_DworczakDACC_bestM
import Definitions.Def_DworczakDACC_bestW

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **The stopping criterion of DACC: every agent holds the best option of its budget set.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017),
Algorithm 1, main block, line 4, p. 8 ("While ∃ i ∈ N, µ(i) ≺ⁱ argmax{Bᵢ; ≻ⁱ} do"), and §3,
p. 7: "The algorithm stops when all agents are matched under µ to the best option in their current
budget set."

`Stopped Mk s` is the negation of the loop guard: every man `d` weakly prefers his partner
`µ(d)` to `argmax{B_d ∪ {∅}}`, and every woman `h` weakly prefers `µ(h)` to `argmax{B_h ∪ {∅}}`.

**Formalization Note.** "Weakly prefers" is `≤` on ranks (smaller is better; ranks are injective,
so `¬ (µ(i) ≺ⁱ b)` is `rank µ(i) ≤ rank b`). -/
def Stopped (Mk : Market D H) (s : State D H) : Prop :=
  (∀ d, Mk.docRank d (s.mateM d) ≤ Mk.docRank d (bestM Mk d (s.budM d))) ∧
    (∀ h, Mk.hospRank h (s.mateW h) ≤ Mk.hospRank h (bestW Mk h (s.budW h)))

/-- The stopping criterion is decidable (a finite conjunction of rank comparisons). -/
instance (Mk : Market D H) : DecidablePred (Stopped Mk) := fun s => by
  unfold Stopped; infer_instance

end DworczakDACC


