-- Prove2me | Definitions.Def_SubmodOrder_marginal
-- name    : SubmodOrder_marginal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:52.612673+00:00
-- url     : https://prove2.me/theorems/e0f48c1a-e15c-493b-943b-dc29bfa8aa70
-- title:
--   Marginal value $f(X\mid S)$
-- statement:
--   Let $f$ be a real set function on a ground set $N$. The **marginal value** of a set $X$ with respect to a set $S$ is
--
--   $$
--   f(X\mid S)=f(X\cup S)-f(S).
--   $$
--
--   For an element $e$ one writes $f(e\mid S)=f(\{e\}\mid S)$. Every inequality of the paper about submodular orders and every test of the Threshold Add algorithm is phrased with marginal values.
--
--   **Formalization Note** Subsets of the ground set are `Finset α`, and $f(e\mid S)$ is `marginal f {e} S`.
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, p.3, "We define the marginal value function, f(X|S) = f(X ∪ S) − f(S)."

import Mathlib

namespace SubmodOrder

/-- The marginal value function `f(X | S) = f(X ∪ S) − f(S)` of a set function `f`
(Udwani, *Submodular Order Functions and Assortment Optimization*, arXiv:2107.02743v5, p.3:
"We define the marginal value function, f(X|S) = f(X ∪ S) − f(S).").

**Formalization Note.** Subsets of the ground set are `Finset α`; `f(e | S)` for an element `e`
is `marginal f {e} S`. -/
def marginal {α : Type*} [DecidableEq α] (f : Finset α → ℝ) (X S : Finset α) : ℝ :=
  f (X ∪ S) - f S

end SubmodOrder


