-- Prove2me | Definitions.Def_ContextualAuctions_PoA_Welfare
-- name    : ContextualAuctions_PoA_Welfare
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:34.805551+00:00
-- url     : https://prove2.me/theorems/8f64f9d0-6876-43fc-90bb-8ec6d62323d1
-- title:
--   §5 — fractional allocations, liquid welfare, and equilibrium allocation
-- statement:
--   An **allocation** $x$ assigns, to each context $\alpha$ and buyer-type profile $(\theta_1,\ldots,\theta_n)$, nonnegative shares $x_i$ summing to one. It is measurable. For buyer $i$ of type $\theta_i=(w_i,B_i)$, first average $w_i^\top\alpha\,x_i$ over the context and the other buyers' types. Then cap that interim value at $B_i$ and average over $\theta_i$. The resulting **liquid welfare** is
--   $$
--   \mathrm{LW}(x)=\sum_{i=1}^{n}\mathbb E_{\theta_i}\!\left[\min\left\{\mathbb E_{\alpha,\theta_{-i}}[w_i^\top\alpha\,x_i(\alpha,\theta_i,\theta_{-i})],B_i\right\}\right].
--   $$
--   For a pacing function $\mu$, the equilibrium allocation $x^\mu$ awards the item to a highest bidder using $\beta^\mu$, splitting any tie evenly. It is the allocation used in the price-of-anarchy comparison of Definition 6.
--
--   **Formalization Note** The simplex is closed and permits zero shares, correcting the paper's inconsistent use of $\mathbb R_+$. The paper's ties have probability zero in equilibrium; equal splitting supplies a feasible value on tie profiles. Interim value is integrated with the buyer's own type fixed.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 13, §5, Definitions 5–6

import Mathlib
import Definitions.Def_ContextualAuctions_PoA_FixedPoint

namespace ContextualAuctions.PoA

open MeasureTheory
open Classical

noncomputable section

abbrev Profile (M : Model) := Fin M.n → Buyer M
abbrev Allocation (M : Model) := Context M → Profile M → Fin M.n → ℝ

/-- A measurable fractional allocation into the closed `n`-simplex on the model domain. -/
def IsAllocation (M : Model) (x : Allocation M) : Prop :=
  Measurable (Function.uncurry x) ∧
    ∀ α ∈ M.A, ∀ θs : Profile M, (∀ i, θs i ∈ Theta M) →
      x α θs ∈ stdSimplex ℝ (Fin M.n)

/-- Interim expected value for buyer `i` of fixed type `θi`. -/
def inner (M : Model) (x : Allocation M) (i : Fin M.n) (θi : Buyer M) : ℝ :=
  ∫ p : Context M × Profile M,
    val M θi p.1 * x p.1 (Function.update p.2 i θi) i
      ∂(M.F.prod (Measure.pi fun _ : Fin M.n => M.G))

/-- Liquid welfare of Definition 5: the budget cap is inside the type expectation. -/
def LW (M : Model) (x : Allocation M) : ℝ :=
  ∑ i : Fin M.n, ∫ θi, min (inner M x i θi) θi.2 ∂M.G

/-- The highest-bid allocation, splitting ties evenly. -/
def xmu (M : Model) (μ : Buyer M → ℝ) : Allocation M :=
  fun α θs i =>
    if ∀ j : Fin M.n, beta M μ (θs j) α ≤ beta M μ (θs i) α then
      1 / (((Finset.univ.filter fun j : Fin M.n =>
        ∀ k : Fin M.n, beta M μ (θs k) α ≤ beta M μ (θs j) α).card : ℕ) : ℝ)
    else 0

end
end ContextualAuctions.PoA


