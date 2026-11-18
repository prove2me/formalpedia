-- Prove2me | Definitions.Def_LostSalesRQ_lower_curve
-- name    : LostSalesRQ_lower_curve
-- status  : Definition
-- author  : @Ming Hu
-- created : 2026-11-17T18:22:48.524597+00:00
-- url     : https://prove2.me/theorems/eb227217-26f1-4801-8d87-1bfa89a7dfea
-- title:
--   Committed-supply bound quantities $B_\mu$, $D_\mu$ and the concave lower curve $\mathcal L_\mu$
-- statement:
--   For a lead-time demand mean $\mu\ge0$ and a rank weight $\eta$, with $p_i,F_i,G_l$ the Poisson functions of the companion definition file:
--
--   1. The rank bound (eq. (8))
--   $$B_\mu(\eta)=\min_{l\ge0}\big\{G_l(\mu)+\eta\,\mathbb P(N(\mu)\ge l)\big\}.$$
--   2. The aging-rate supremum (eq. (9)), over the number $m\ge0$ of pending units and ordered residual delivery times,
--   $$D_\mu(\eta)=\sup_{m\ge0,\ 0\le\tau_1\le\cdots\le\tau_m\le\mu}\ \sum_{i=1}^{m}\big(\eta\,p_{i-1}(\tau_i)-F_{i-1}(\tau_i)\big),$$
--   the empty sum ($m=0$) included.
--   3. The concave lower curve (eq. (13))
--   $$\mathcal L_\mu(a)=\sup_{\eta\ge1}\min\{B_\mu(\eta),\,a-D_\mu(\eta)\}.$$
--
--   Proposition 1 shows that $\min\{B_\mu(\eta),a-D_\mu(\eta)\}$ bounds the zero-setup optimal cost from below for every $\eta\ge1$, so $\mathcal L_\mu(a)$ is the best such bound.
--
--   **Formalization Note** The minimum in (8) is a real infimum over $l\in\mathbb N$ (bounded below by $0$ for $\eta\ge0$). The suprema in (9) and (13) are real suprema of explicit sets that are nonempty and bounded above on the paper's domain ($D_\mu(\eta)\le\eta^2/2-\eta/3$ and $\mathcal L_\mu(a)\le a$); in the Lean sum over $i:\mathrm{Fin}\,m$ the index $i$ carries rank $i+1$.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 4.3.1, eqs. (8)-(9) (pp. 11-12); Section 4.3.3, eq. (13) (p. 14).

import Definitions.Def_LostSalesRQ_poisson_functions

/-!
# The committed-supply lower-bound quantities

`B_μ(η)` (eq. (8)), `D_μ(η)` (eq. (9)) and the concave lower curve `𝓛_μ(a)` (eq. (13)) of
M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems".
-/

namespace LostSalesRQ

open Finset

/-- Rank bound `B_μ(η) = min_{l ≥ 0} {G_l(μ) + η P(N(μ) ≥ l)}` (eq. (8)). -/
noncomputable def rankBound (μ η : ℝ) : ℝ :=
  ⨅ l : ℕ, (expectedShortfall μ l + η * poisTail μ l)

/-- Aging-rate supremum (eq. (9)): the supremum, over the number `m ≥ 0` of pending units and
ordered residual delivery times `0 ≤ τ_1 ≤ ⋯ ≤ τ_m ≤ μ`, of
`∑_{i=1}^{m} (η p_{i-1}(τ_i) - F_{i-1}(τ_i))`. Here `Fin m` indexes the ranks `1, …, m`
from `0`, so index `i` carries rank `i + 1`. -/
noncomputable def agingRateSup (μ η : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ (m : ℕ) (τ : Fin m → ℝ), Monotone τ ∧ (∀ i, 0 ≤ τ i ∧ τ i ≤ μ) ∧
    x = ∑ i : Fin m, (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ))}

/-- Concave lower curve `𝓛_μ(a) = sup_{η ≥ 1} min{B_μ(η), a - D_μ(η)}` (eq. (13)). -/
noncomputable def lowerCurve (μ a : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ η : ℝ, 1 ≤ η ∧ x = min (rankBound μ η) (a - agingRateSup μ η)}

end LostSalesRQ


