-- Prove2me | Definitions.Def_ScalarMultiRisk_acceptanceSet
-- name    : ScalarMultiRisk_acceptanceSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:05.76809+00:00
-- url     : https://prove2.me/theorems/4aac00f6-55eb-4927-9ead-dfe650865921
-- title:
--   The acceptance set of an extended-valued map
-- statement:
--   For a map $r$ on $L^\infty(E)$ with extended real values, its **acceptance set** is $\{X\in L^\infty(E)\mid r(X)\le0\text{ a.s.}\}$. The sets $A_t$, $A^\pi_t$ and $A^\phi_t$ all have this form.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Proposition 4.5, p.19

import Mathlib
import Definitions.Def_ScalarMultiRisk_LinftyFull

open MeasureTheory

namespace ScalarMultiRisk

/-- **Acceptance set of a map.** `{X ∈ L∞(E) | r(X) ≤ 0 a.s.}`. arXiv:1807.10694v5: this is the
form of `A^π_t` (Prop 4.5, p.19) and `A^φ_t` (p.22), and of `A_t` by Assumption 3.3 (p.8).

**Formalization Note.** The maps are `EReal`-valued because `π^S_t` is (Definition 4.2). -/
def acceptanceSet {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {E : Type*} [NormedAddCommGroup E]
    (B : FilteredSpace Ω T) (r : (Ω → E) → Ω → EReal) : Set (Ω → E) :=
  {X ∈ LinftyFull B (Fin.last T) | r X ≤ᵐ[B.P] 0}

end ScalarMultiRisk


