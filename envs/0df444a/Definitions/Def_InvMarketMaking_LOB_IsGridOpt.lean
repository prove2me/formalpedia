-- Prove2me | Definitions.Def_InvMarketMaking_LOB_IsGridOpt
-- name    : InvMarketMaking_LOB_IsGridOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:28.01389+00:00
-- url     : https://prove2.me/theorems/96bfe561-1cd8-4316-86ea-21561801daba
-- title:
--   Virtual optimal bid–ask pair $(b^\circ,a^\circ)\in\arg\max_{\mathcal B^\circ\times\mathcal A^\circ}J$
-- statement:
--   Let $\mathcal B^\circ,\mathcal A^\circ\subset[0,1]$ be finite sets of bids and asks. A pair $(b^\circ,a^\circ)$ is a **virtual optimal pair** on these grids if
--   $$
--   (b^\circ,a^\circ)\in\operatorname*{argmax}_{b\in\mathcal B^\circ,\ a\in\mathcal A^\circ}J(b,a),
--   $$
--   that is, $b^\circ\in\mathcal B^\circ$, $a^\circ\in\mathcal A^\circ$ and $J(b',a')\le J(b^\circ,a^\circ)$ for all $b'\in\mathcal B^\circ$, $a'\in\mathcal A^\circ$.
--
--   The pair need not be unique; statements quantified over every pair satisfying this predicate hold regardless of how ties are broken.
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Definition 4.4, Eq. (7), p. 19

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_J

namespace InvMarketMaking.LOB

open MeasureTheory

/-- `(b, a)` is a virtual optimal bid-ask pair on the grids `Bg = B°`, `Ag = A°`:
`(b°, a°) ∈ argmax_{b ∈ B°, a ∈ A°} J(b, a)` (Maran, Restelli, Stradi, arXiv:2610.24562v1,
Definition 4.4, Eq. (7), p. 19).

**Formalization Note** The predicate holds for every maximizer, so a statement quantified over all
`(b, a)` with `IsGridOpt V Bg Ag b a` holds "regardless of how ties are broken" (p. 19). -/
def IsGridOpt (V : Measure (ℝ × ℝ)) (Bg Ag : Finset ℝ) (b a : ℝ) : Prop :=
  b ∈ Bg ∧ a ∈ Ag ∧ ∀ b' ∈ Bg, ∀ a' ∈ Ag, J V b' a' ≤ J V b a

end InvMarketMaking.LOB


