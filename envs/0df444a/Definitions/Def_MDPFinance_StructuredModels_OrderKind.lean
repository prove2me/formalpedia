-- Prove2me | Definitions.Def_MDPFinance_StructuredModels_OrderKind
-- name    : MDPFinance_StructuredModels_OrderKind
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:35:41.456603+00:00
-- url     : https://prove2.me/theorems/5b9d2129-6d3e-4778-b5ed-a9dfb0f51837
-- title:
--   The three orders $\diamond \in \{\mathrm{st}, \mathrm{cv}, \mathrm{cx}\}$ of Theorem 2.4.23
-- statement:
--   `OrderKind` names the three cases $\diamond \in \{\mathrm{st}, \mathrm{cv}, \mathrm{cx}\}$ of
--   Theorem 2.4.23. $\mathrm{I\!M}^\diamond_n$ is $\{v \in \mathbb{I\!B}_b^+ : v \text{
--   increasing}\}$, $\{v \text{ concave}\}$, $\{v \text{ convex}\}$ according to $\diamond$; the
--   order $\leq_\diamond$ is $\leq_{\mathrm{st}}$, $\leq_{\mathrm{cv}}$, $\leq_{\mathrm{cx}}$
--   correspondingly.
--
--   **Formalization Note.** A bookkeeping device packaging the book's own three-way case split
--   into one theorem statement (Theorem 2.4.23 is proved identically in all three cases).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 38, Theorem 2.4.23

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_ConvexAnalysis
import Definitions.Def_MDPFinance_StructuredModels_StochasticOrders

open MeasureTheory

namespace MDPFinance.StructuredModels

/-- The three stochastic orders of Theorem 2.4.23 (Bäuerle–Rieder, p. 38, PDF 53), bundled into
one tag `⋄ ∈ {st, cv, cx}` matching the book's own three-way case split (`IM_n^st`, `IM_n^cv`,
`IM_n^cx`). -/
inductive OrderKind
  | st
  | cv
  | cx

variable {E : Type*} [MeasurableSpace E] [Preorder E] [AddCommGroup E] [Module ℝ E]

/-- The set `IM_n^⋄` of Theorem 2.4.23: increasing, concave or convex functions of `IB_b^+`,
according to `⋄`. -/
def IMDiamond (b : E → ℝ) : OrderKind → Set (E → EReal)
  | .st => {v ∈ IBbPlus b | Monotone v}
  | .cv => {v ∈ IBbPlus b | ConcaveOnEReal Set.univ v}
  | .cx => {v ∈ IBbPlus b | ConvexOnEReal Set.univ v}

/-- The order `≤_⋄` of Theorem 2.4.23, according to `⋄`. -/
def LEDiamond : OrderKind → Measure E → Measure E → Prop
  | .st => LEStochasticOrder
  | .cv => LEConcaveOrder
  | .cx => LEConvexOrder

end MDPFinance.StructuredModels


