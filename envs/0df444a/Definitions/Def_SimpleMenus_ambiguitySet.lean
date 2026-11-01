-- Prove2me | Definitions.Def_SimpleMenus_ambiguitySet
-- name    : SimpleMenus_ambiguitySet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:57.597317+00:00
-- url     : https://prove2.me/theorems/8ee6bb0e-82fd-4c12-ad9a-0f2ef1194125
-- title:
--   Ambiguity set $\mathcal F$ of (2)
-- statement:
--   Given functions $\phi_1,\dots,\phi_K$ of the valuation, the ambiguity set is
--
--   $$\mathcal F=\Bigl\{F\in\mathcal P([0,\bar v])\;:\;\int_{[0,\bar v]}\phi_k(w)\,dF(w)\ge 0,\ k=1,\dots,K\Bigr\}.$$
--
--   It encodes the seller's partial information on the buyer's valuation distribution: support, mean, quantile, multi-segment and segmented-mean information are all of this form.
--
--   **Formalization Note** A law on $[0,\bar v]$ is a Borel probability measure on $\mathbb R$ that gives no mass to the complement of $[0,\bar v]$. Each constraint also requires $\phi_k$ to be integrable, so the integral is the true one; under Assumption 1 this holds for every such law. $K=0$ is allowed.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, display (2), p.9

import Mathlib

open MeasureTheory Set

namespace SimpleMenus

/-- The ambiguity set (2): the probability measures `F` on `[0, v̄]` with
`∫_{[0, v̄]} ϕ_k dF ≥ 0` for every `k = 1, …, K` (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, display (2), p.9).

Formalization Note: a law on `[0, v̄]` is a probability measure on `ℝ` (Borel) giving no mass to
the complement of `[0, v̄]`. The constraint functions are indexed by `Fin K`, `K = 0` allowed.
Each constraint carries `Integrable (ϕ k) F`, so that the Bochner integral is the true one; under
Assumption 1 (bounded, piecewise monotone `ϕ_k`) it holds for every such `F`. -/
def ambiguitySet (vbar : ℝ) {K : ℕ} (phi : Fin K → ℝ → ℝ) : Set (Measure ℝ) :=
  {F | IsProbabilityMeasure F ∧ F (Icc 0 vbar)ᶜ = 0 ∧
      ∀ k, Integrable (phi k) F ∧ 0 ≤ ∫ w, phi k w ∂F}

end SimpleMenus


