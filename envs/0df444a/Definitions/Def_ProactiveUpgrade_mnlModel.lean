-- Prove2me | Definitions.Def_ProactiveUpgrade_mnlModel
-- name    : ProactiveUpgrade_mnlModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:53.493545+00:00
-- url     : https://prove2.me/theorems/fd72a2e6-3215-49f8-9a23-3766f2fa1ad1
-- title:
--   The MNL model: $\beta_i$, $\beta_0$ and $q_i$ from (1)–(3)
-- statement:
--   Customer utilities are $U_i=a_i-bp_i+\epsilon_i$ with i.i.d. standard Gumbel noise. The multinomial-logit request and no-request probabilities are
--
--   $$
--   \beta_i=\frac{\exp(a_i-bp_i)}{1+\sum_{k\in\mathcal M}\exp(a_k-bp_k)},\qquad \beta_0=\frac{1}{1+\sum_{k\in\mathcal M}\exp(a_k-bp_k)},
--   $$
--
--   and the probability that a customer who requested $i<m$ accepts a free upgrade to $i+1$ is
--
--   $$
--   q_i=\frac{\exp(a_{i+1}-bp_i)-\exp(a_{i+1}-bp_{i+1})}{1+\exp(a_{i+1}-bp_i)+\sum_{k\in\mathcal M\setminus\{i+1\}}\exp(a_k-bp_k)},
--   $$
--
--   with $q_m=0$. The model `mnlModel a b p λ` carries these probabilities together with the prices $p$ and the arrival probability $\lambda$.
--
--   **Formalization Note** $q_i$ is taken from formula (3), as the paper's operators (8) and (12) do ("where $q_i$ is given in (3)"); the Gumbel derivation of (3) (Proposition 1) is not formalized.
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, eqs. (1), (2), p.7; eq. (3), p.9; Proof of Proposition 1, p.34

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model

namespace ProactiveUpgrade

/-- MNL request probability (eq. (1), p.7):
`βᵢ = exp(aᵢ − bpᵢ) / (1 + Σ_{k∈M} exp(a_k − bp_k))`. -/
noncomputable def mnlBeta {m : ℕ} (a : Fin m → ℝ) (b : ℝ) (p : Fin m → ℝ) (i : Fin m) : ℝ :=
  Real.exp (a i - b * p i) / (1 + ∑ k, Real.exp (a k - b * p k))

/-- MNL no-request probability (eq. (2), p.7): `β₀ = 1 / (1 + Σ_{k∈M} exp(a_k − bp_k))`. -/
noncomputable def mnlBeta0 {m : ℕ} (a : Fin m → ℝ) (b : ℝ) (p : Fin m → ℝ) : ℝ :=
  1 / (1 + ∑ k, Real.exp (a k - b * p k))

/-- Upgrade acceptance probability (eq. (3), p.9): for `i < m`,
`qᵢ = [exp(a_{i+1} − bpᵢ) − exp(a_{i+1} − bp_{i+1})] /
[1 + exp(a_{i+1} − bpᵢ) + Σ_{k∈M∖{i+1}} exp(a_k − bp_k)]`, and `q_m = 0` (Proof of
Proposition 1, p.34: "we set q_m = 0"). -/
noncomputable def mnlQ {m : ℕ} (a : Fin m → ℝ) (b : ℝ) (p : Fin m → ℝ) (i : Fin m) : ℝ :=
  if h : i.val + 1 < m then
    (Real.exp (a (succIdx i h) - b * p i) - Real.exp (a (succIdx i h) - b * p (succIdx i h))) /
      (1 + Real.exp (a (succIdx i h) - b * p i) +
        ∑ k ∈ Finset.univ.erase (succIdx i h), Real.exp (a k - b * p k))
  else 0

/-- **The MNL model** (Chen et al., SSRN 3777846, eqs. (1)–(3), pp.7–9): utilities
`Uᵢ = aᵢ − bpᵢ + εᵢ` with i.i.d. Gumbel `εᵢ`, prices `p`, arrival probability `λ`; `β`, `β₀`
from (1), (2) and `q` from (3).

**Formalization Note** `q` is taken from formula (3) as the paper's (8) and (12) do ("where qᵢ is
given in (3)"); the Gumbel derivation (Proposition 1) is not formalized. -/
noncomputable def mnlModel {m : ℕ} (a : Fin m → ℝ) (b : ℝ) (p : Fin m → ℝ) (lam : ℝ) : Model m where
  p := p
  β := mnlBeta a b p
  β0 := mnlBeta0 a b p
  q := mnlQ a b p
  lam := lam

end ProactiveUpgrade


