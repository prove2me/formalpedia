-- Prove2me | Definitions.Def_DDROCS_SimultaneouslyImplies
-- name    : DDROCS_SimultaneouslyImplies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:29:30.716071+00:00
-- url     : https://prove2.me/theorems/3147a5a4-75f0-4c89-8f79-a8dcdc5f5c0e
-- title:
--   A family of sets simultaneously implies a probabilistic guarantee
-- statement:
--   Let $\mathbb P$ be a measure on $\mathbb R^d$ and let $\{\mathcal U(\epsilon) : 0<\epsilon<1\}$ be a family of subsets of $\mathbb R^d$. The family **simultaneously implies a probabilistic guarantee for $\mathbb P$** if
--
--   $$
--   \mathcal U(\epsilon) \text{ implies a probabilistic guarantee for } \mathbb P \text{ at level } \epsilon \qquad \text{for every } 0<\epsilon<1 .
--   $$
--
--   Simultaneity lets the level $\epsilon$ be chosen after the data are seen (for instance optimized jointly with the decision), which a guarantee for a single fixed $\epsilon$ does not allow.
--
--   **Formalization Note** The family is a function from $\mathbb R$ to subsets of $\mathbb R^d$; its values outside $0<\epsilon<1$ are never read.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, p. 11 (unnumbered definition)

import Mathlib
import Definitions.Def_DDROCS_ImpliesGuarantee
open MeasureTheory

namespace DDROCS

/-- **A family of sets simultaneously implies a probabilistic guarantee.**
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, p. 11 (unnumbered):
"Given a family of sets indexed by `ϵ`, `{U(ϵ) : 0 < ϵ < 1}`, we say this family simultaneously
implies a probabilistic guarantee for `P∗` if, for all `0 < ϵ < 1`, each `U(ϵ)` implies a
probabilistic guarantee for `P∗` at level `ϵ`."

`SimultaneouslyImplies U P` says `ImpliesGuarantee (U ε) P ε` for every `0 < ε < 1`.

**Formalization Note.** The family is a function `U : ℝ → Set ℝ^d`; its values outside
`0 < ε < 1` are never read. -/
def SimultaneouslyImplies {d : ℕ} (U : ℝ → Set (EuclideanSpace ℝ (Fin d)))
    (P : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ImpliesGuarantee (U ε) P ε

end DDROCS


