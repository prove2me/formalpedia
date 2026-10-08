-- Prove2me | Definitions.Def_RevenueOrdered_Nesting_LStar
-- name    : RevenueOrdered_Nesting_LStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:17:29.94416+00:00
-- url     : https://prove2.me/theorems/8b4bb23c-aaed-4a60-b3c4-07e68fe46fb8
-- title:
--   App. B, p. 35 — 𝓛∗(δ), the optimal revenue-ordered indices when δ is added to every revenue
-- statement:
--   Let $\mathcal P$ be a system of choice probabilities on the products $\mathcal C$, $r$ a revenue function with distinct values $r_1<\cdots<r_k$, and $S_\ell=\{x : r(x)\ge r_\ell\}$ the revenue-ordered assortments. For $\delta\in\mathbb R$, the revenue of $S_\ell$ when $\delta$ is added to the revenue of every item is
--   $$
--   \sum_{x\in S_\ell}\mathcal P(x,S_\ell)\,\bigl(r(x)+\delta\bigr),
--   $$
--   and $\mathcal L^*(\delta)$ is the set of indices $\ell\in[k]$ that maximise it:
--   $$
--   \mathcal L^*(\delta)=\Bigl\{\ell\in[k] : \sum_{x\in S_\ell}\mathcal P(x,S_\ell)(r(x)+\delta)=\max_{\ell'\in[k]}\sum_{x\in S_{\ell'}}\mathcal P(x,S_{\ell'})(r(x)+\delta)\Bigr\}.
--   $$
--   It is a nonempty subset of $[k]$, and $\min\mathcal L^*(\delta)$ is the index of the largest revenue-ordered assortment that is optimal for the shifted revenues.
--
--   In the proof of Theorem 5.1, the choice of offer set at each stage of the multi-period problem is shown to be exactly this shifted single-period problem, with $\delta$ equal to minus the marginal value of capacity.
--
--   **Formalization Note** The paper introduces $\mathcal L^*(\delta)$ only for $\delta$ with $r_k+\delta\ge 0$. The definition here is the displayed formula for every real $\delta$; the results that use it carry the hypothesis $r_k+\delta\ge 0$ where the paper does. `minLStar P r δ` is the minimum, taken with `Finset.min'` and the nonemptiness of the set of maximisers.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 35, Appendix B, definition of 𝓛∗(δ)

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_RevenueOrdered

namespace RevenueOrdered.Nesting

noncomputable section

variable {C : Type*} [Fintype C] [Nonempty C]

/-- `∑_{x ∈ S_ℓ} 𝒫(x, S_ℓ)(r(x) + δ)`: the revenue of the revenue-ordered assortment `S_ℓ`
when `δ` is added to the revenue of every item (App. B, p. 35). -/
def shiftedRevenue (P : C → Finset C → ℝ) (r : C → ℝ) (δ : ℝ) (ℓ : ℕ) : ℝ :=
  ∑ x ∈ RevenueOrdered.Ratio.roSet r ℓ, P x (RevenueOrdered.Ratio.roSet r ℓ) * (r x + δ)

/-- `𝓛∗(δ)` (App. B, p. 35): the set of indices `ℓ ∈ [k]` such that
`∑_{x ∈ S_ℓ} 𝒫(x, S_ℓ)(r(x) + δ) = max_{ℓ' ∈ [k]} ∑_{x ∈ S_ℓ'} 𝒫(x, S_ℓ')(r(x) + δ)`.
The paper introduces it for `δ` with `r_k + δ ≥ 0`; the set is defined here for every `δ`
and the results that use it carry that hypothesis. -/
def lStar (P : C → Finset C → ℝ) (r : C → ℝ) (δ : ℝ) : Finset ℕ :=
  argmaxLevels r (shiftedRevenue P r δ)

/-- `min 𝓛∗(δ)`, the minimum of the nonempty finite set `𝓛∗(δ)`. -/
def minLStar (P : C → Finset C → ℝ) (r : C → ℝ) (δ : ℝ) : ℕ :=
  (lStar P r δ).min' (argmaxLevels_nonempty r _)

end

end RevenueOrdered.Nesting


