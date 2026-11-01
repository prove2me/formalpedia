-- Prove2me | Definitions.Def_ConstrainedTrading_unitBox
-- name    : ConstrainedTrading_unitBox
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:50.44275+00:00
-- url     : https://prove2.me/theorems/e4285e16-e753-4158-981c-f08e322d24f9
-- title:
--   Unit hypercube $N(x)$ containing a real point
-- statement:
--   For $x\in\mathbb R^E$, the **unit hypercube containing $x$** is the set of integer points
--   $$
--   N(x)=\{z\in\mathbb Z^E:\ \lfloor x_e\rfloor\le z_e\le\lceil x_e\rceil\ \ \forall e\in E\}.
--   $$
--   It is the smallest integer box whose convex hull contains $x$; for integral $x_e$ the $e$-th side is the single value $x_e$.
--
--   **Formalization Note** The paper names $N(x)$ in Definition 2.10 without a formula; this is the reading used.
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, Definition 2.10, p.6 ("N(x) is the unit hypercube containing x")

import Mathlib

namespace ConstrainedTrading

/-- The **unit hypercube containing `x`**, `N(x) = {z ∈ ℤ^E : ⌊x_e⌋ ≤ z_e ≤ ⌈x_e⌉ ∀ e}`
(Kizilkale–Vohra, *Constrained Trading Networks*, arXiv:2008.09757v1, Definition 2.10, p.6:
"N(x) is the unit hypercube containing x").

**Formalization Note** The page names `N(x)` without a formula; it is read as the smallest
integer box containing `x`. For integral `x_e` the `e`-th side collapses to the single value
`x_e`. -/
def unitBox {E : Type*} (x : E → ℝ) : Set (E → ℤ) :=
  {z | ∀ e, ⌊x e⌋ ≤ z e ∧ z e ≤ ⌈x e⌉}

end ConstrainedTrading


