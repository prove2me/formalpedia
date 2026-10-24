-- Prove2me | Definitions.Def_ContextualAuctions_PoA_SecondPrice
-- name    : ContextualAuctions_PoA_SecondPrice
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-23T06:34:37.476664+00:00
-- url     : https://prove2.me/theorems/7f8a8d35-2033-494d-8319-bc5d220ba03c
-- title:
--   Appendix D — second-highest paced value $p(\alpha,\tilde\theta)$ and interim price weight
-- statement:
--   Fix a contextual auction model with $n\ge 2$ buyers and a pacing function $\mu$. For an item (context) $\alpha$ and a buyer-type profile $\tilde\theta=(\theta_1,\dots,\theta_n)$, $\theta_i=(w_i,B_i)$, the paced values are $v_i=w_i^\top\alpha/(1+\mu(w_i,B_i))$. This file defines two objects used in the proof of the liquid-welfare price-of-anarchy bound.
--
--   1. The **second-highest paced value** $p(\alpha,\tilde\theta)$: the second largest element, counted with multiplicity, of $\{v_1,\dots,v_n\}$. It is the price paid in the second-price auction of the equilibrium parameterized by $\mu$. Equivalently,
--   $$
--   p(\alpha,\tilde\theta)=\max_{i\neq j}\ \min(v_i,v_j).
--   $$
--
--   2. For a fractional allocation $x$, a buyer $i$ and a fixed type $\theta_i$, the **interim price weight**
--   $$
--   \mathbb E_{\alpha,\theta_{-i}}\big[p(\alpha,\theta_i,\theta_{-i})\,x_i(\alpha,\theta_i,\theta_{-i})\big],
--   $$
--   where $\alpha\sim F$ and the other buyers' types are i.i.d. $G$.
--
--   The term in item 2 is subtracted on the right-hand side of Lemma 13. Summing it over buyers and averaging over $\theta_i$ gives the expected revenue $\mathbb E[p]$, for any allocation that sums to one.
--
--   **Formalization Note** The maximum over ordered pairs of distinct indices is written as a real `iSup` over a finite type. In the expectation, the profile is drawn from $F\otimes G^{n}$ and coordinate $i$ is overwritten by $\theta_i$ (`Function.update`), which matches how `inner` in the welfare definitions is written.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science (2023), doi:10.1287/mnsc.2023.4719; arXiv:2102.10476, Appendix D, Proof of Theorem 3 (p. ec19: definition of p(α, θ̃) and the right-hand side of Lemma 13)

import Mathlib
import Definitions.Def_ContextualAuctions_PoA_Welfare

namespace ContextualAuctions.PoA

open MeasureTheory
open Classical

noncomputable section

/-- The second-highest paced value `p(α, θ̃)` of Appendix D: the second largest element
(counted with multiplicity) of `{wᵢᵀα / (1 + μ(wᵢ, Bᵢ)) | i ∈ [n]}`, written as the largest
minimum over pairs of distinct buyers. -/
def secondPaced (M : Model) (μ : Buyer M → ℝ) (α : Context M) (θs : Profile M) : ℝ :=
  ⨆ ij : {ij : Fin M.n × Fin M.n // ij.1 ≠ ij.2},
    min (paced M μ (θs ij.1.1) α) (paced M μ (θs ij.1.2) α)

/-- The interim expected second-price payment weight
`E_{α, θ₋ᵢ}[p(α, θᵢ, θ₋ᵢ) · xᵢ(α, θᵢ, θ₋ᵢ)]` of buyer `i` with fixed type `θᵢ`. -/
def interimPrice (M : Model) (μ : Buyer M → ℝ) (x : Allocation M) (i : Fin M.n)
    (θi : Buyer M) : ℝ :=
  ∫ p : Context M × Profile M,
    secondPaced M μ p.1 (Function.update p.2 i θi) * x p.1 (Function.update p.2 i θi) i
      ∂(M.F.prod (Measure.pi fun _ : Fin M.n => M.G))

end
end ContextualAuctions.PoA


