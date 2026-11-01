-- Prove2me | Definitions.Def_ConstrainedTrading_linearValuation
-- name    : ConstrainedTrading_linearValuation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:51.121985+00:00
-- url     : https://prove2.me/theorems/0f2161dd-178c-4f8d-b299-fd29ee43d746
-- title:
--   Linear valuation $w(y)=\sum_e c_e y_e$
-- statement:
--   For a finite index set $\iota$ and a coefficient vector $c\in\mathbb R^\iota$, the **linear valuation** is
--   $$
--   w(y)=\sum_{e\in\iota}c_e\,y_e\qquad(y\in\mathbb Z^\iota),
--   $$
--   regarded as a function into $\mathbb R\cup\{-\infty\}$ that is finite everywhere. In §3 the valuations $w_2$ and $w_i^-$ are linear.
--
--   **Formalization Note** "Linear" is read in the strict sense, with no constant term.
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, §3, pp.7–8 ("w2(y2) is linear", "w−i is linear")

import Mathlib

namespace ConstrainedTrading

/-- The **linear valuation** `w(y) = Σ_{e} c_e y_e` on `ℤ^ι` with coefficient vector `c ∈ ℝ^ι`,
as a function into `ℝ ∪ {−∞}` (finite everywhere). Kizilkale–Vohra, *Constrained Trading
Networks*, arXiv:2008.09757v1, §3, pp.7–8: "w₂(y²) is linear", "w⁻ᵢ is linear".

**Formalization Note** "Linear" is read as linear in the strict sense (no constant term). -/
def linearValuation {ι : Type*} [Fintype ι] (c : ι → ℝ) : (ι → ℤ) → WithBot ℝ :=
  fun y => ((∑ e, c e * (y e : ℝ) : ℝ) : WithBot ℝ)

end ConstrainedTrading


