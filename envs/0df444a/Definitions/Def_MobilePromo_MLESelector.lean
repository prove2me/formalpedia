-- Prove2me | Definitions.Def_MobilePromo_MLESelector
-- name    : MobilePromo_MLESelector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:40.114696+00:00
-- url     : https://prove2.me/theorems/963d206d-defc-4f3b-a5bc-7c753c82c65f
-- title:
--   Maximum-likelihood selectors and the i.i.d. law of the exploration data
-- statement:
--   A **maximum-likelihood selector** gives, for each location $l$, cycle $s$ and data $\boldsymbol D_l(1),\dots,\boldsymbol D_l(s)\in\{0,1\}^{k_l}$, a point
--
--   $$
--   \hat\gamma_l(s)\in\arg\max_{\gamma_l\in\Gamma_l^{(0)}}\prod_{\hat s=1}^sQ_l^{\bar{\boldsymbol b}_l,\gamma_l}(\boldsymbol D_l(\hat s)).
--   $$
--
--   We write $\hat\gamma(s)=(\hat\gamma_1(s),\dots,\hat\gamma_L(s))$. The i.i.d. expectation is the one under which the vectors $\boldsymbol D_l(\hat s)$ are independent across $\hat s$ and $l$, with law $Q_l^{\bar{\boldsymbol b}_l,\gamma_l}$.
--
--   **Formalization Note** The arg max need not be unique, so the choice among maximizers is an input of the policy, with its maximization property, rather than a hidden convention.
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, p.17; heading and Lemma 3, p.18

import Mathlib
import Definitions.Def_MobilePromo_Exploration

set_option autoImplicit false

namespace MobilePromo

/-- A maximum-likelihood estimator (SSRN 3523491, p.17): for each location `l`, cycle `s` and data
`D_l(1), …, D_l(s) ∈ {0,1}^{k_l}`, a point `γ̂_l(s)` of `Γ_l⁽⁰⁾` maximizing `∏_{ŝ} Q_l^{b̄_l, γ_l}(D_l(ŝ))`.

**Formalization Note** The arg max need not be unique, so the choice among maximizers is an input of
`bidAlloc`. -/
structure MLESelector (M : Model) (X : Exploration M) where
  /-- The estimate. -/
  est : (l : Fin M.L) → (s : ℕ) → (Fin s → Fin (X.k l) → Bool) → Param (M.n l)
  mem : ∀ l s D, est l s D ∈ M.Γ₀ l
  isMax : ∀ l s D, ∀ γ ∈ M.Γ₀ l,
    ∏ ŝ, Q M l (X.bbar l) γ (D ŝ) ≤ ∏ ŝ, Q M l (X.bbar l) (est l s D) (D ŝ)

/-- The vector `γ̂(s) = (γ̂₁(s), …, γ̂_L(s))` of estimates on the data `D` (SSRN 3523491, p.17). -/
noncomputable def mleVec (M : Model) (X : Exploration M) (mle : MLESelector M X) (s : ℕ)
    (D : (l : Fin M.L) → Fin s → Fin (X.k l) → Bool) : M.ParamVec :=
  WithLp.toLp 2 fun l => mle.est l s (D l)

/-- The expectation under the i.i.d. law of Lemma 3: the data
`D_l(1), …, D_l(s)` are independent, across `ŝ` and across locations, with `D_l(ŝ)` of law
`Q_l^{b̄_l, γ_l}` (SSRN 3523491, pp.17–18). -/
noncomputable def iidExp (M : Model) (X : Exploration M) (γ : M.ParamVec) (s : ℕ)
    (F : ((l : Fin M.L) → Fin s → Fin (X.k l) → Bool) → ℝ) : ℝ :=
  ∑ D, (∏ l, ∏ ŝ, Q M l (X.bbar l) (γ l) (D l ŝ)) * F D

end MobilePromo


