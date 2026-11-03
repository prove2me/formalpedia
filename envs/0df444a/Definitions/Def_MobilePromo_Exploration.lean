-- Prove2me | Definitions.Def_MobilePromo_Exploration
-- name    : MobilePromo_Exploration
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:44.330693+00:00
-- url     : https://prove2.me/theorems/7b4ef67f-fcbf-425d-af72-e647dfb5cb86
-- title:
--   The outcome law $Q_l^{b,\gamma_l}$ and the exploration bids
-- statement:
--   For a fixed sequence of bids $\boldsymbol b=(b_1,\dots,b_k)\in B^k$ at location $l$, the outcome $\boldsymbol D\in\{0,1\}^k$ of the $k$ bids has the law
--
--   $$
--   Q_l^{\boldsymbol b,\gamma_l}(\boldsymbol d)=\prod_{\hat k=1}^k p_l(\gamma_l,b_{\hat k})^{d_{\hat k}}\bigl(1-p_l(\gamma_l,b_{\hat k})\bigr)^{1-d_{\hat k}} .
--   $$
--
--   The **exploration bids** are, for each location $l$, a vector $\bar{\boldsymbol b}_l=(\bar b_l^1,\dots,\bar b_l^{k_l})\in B^{k_l}$ with $k_l\ge 1$. They are the input of the policy BidAlloc, which places them repeatedly to estimate $\gamma_l$.
--
--   **Formalization Note** The condition $k_l\ge1$ is implicit in the paper. The law $Q$ takes an arbitrary bid vector; the exploration bids are the structure `Exploration`.
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, p.12 and "Input", p.17

import Mathlib
import Definitions.Def_MobilePromo_Model

set_option autoImplicit false

namespace MobilePromo

/-- The law of the outcomes of a fixed sequence of bids (SSRN 3523491, p.12):
`Q_l^{b, γ_l}(d) = ∏_{k̂} p_l(γ_l, b_{k̂})^{d_{k̂}} (1 - p_l(γ_l, b_{k̂}))^{1 - d_{k̂}}`. -/
noncomputable def Q (M : Model) (l : Fin M.L) {k : ℕ} (b : Fin k → ℝ) (γl : Param (M.n l))
    (d : Fin k → Bool) : ℝ :=
  ∏ j, if d j then M.p l γl (b j) else 1 - M.p l γl (b j)

/-- The exploration bids of the policy: for each location `l`, a vector
`b̄_l = (b̄_l¹, …, b̄_l^{k_l}) ∈ B^{k_l}` (SSRN 3523491, Assumption 2, p.12, and "Input", p.17).

**Formalization Note** `k_pos` is implicit in the paper: the exploration phase needs a bid to place. -/
structure Exploration (M : Model) where
  /-- The number `k_l` of exploration bids at `l`. -/
  k : Fin M.L → ℕ
  k_pos : ∀ l, 0 < k l
  /-- The exploration bids at `l`. -/
  bbar : (l : Fin M.L) → Fin (k l) → ℝ
  bbar_mem : ∀ l j, bbar l j ∈ M.B

end MobilePromo


