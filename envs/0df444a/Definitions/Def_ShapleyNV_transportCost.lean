-- Prove2me | Definitions.Def_ShapleyNV_transportCost
-- name    : ShapleyNV_transportCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:26.919412+00:00
-- url     : https://prove2.me/theorems/563c9b05-f81f-4f9f-81ca-ea1feb671576
-- title:
--   Optimal transport cost $\inf_{\gamma\in\Gamma(\mathbb P,\mathbb Q)}\mathbb E_\gamma[c]$
-- statement:
--   Let $c$ be a nonnegative ground cost on a measurable space $E$, and let $\mathbb P, \mathbb Q$ be measures on $E$. Write $\Gamma(\mathbb P, \mathbb Q)$ for the set of probability measures on $E \times E$ with marginals $\mathbb P$ and $\mathbb Q$ (couplings). The optimal transport cost is
--
--   $$
--   W_c(\mathbb P, \mathbb Q) := \inf_{\gamma \in \Gamma(\mathbb P, \mathbb Q)} \mathbb E_{(\xi, \xi') \sim \gamma}\big[c(\xi, \xi')\big] \in [0, \infty].
--   $$
--
--   With $c((x,z),(x',z')) = \|x-x'\| + |z-z'|$ this is the type-1 Wasserstein distance $\mathcal W$ of the paper, eq. (3).
--
--   **Formalization Note** The couplings are the published platform definition `WassersteinDRO.StrongDuality.couplings`. The value is an extended nonnegative real; the costs of this mission are sums of distances, so taking their nonnegative part changes nothing.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), §2.2, eq. (3), p.5, and the definition of Γ(P, Q), p.6

import Mathlib
import Definitions.Def_WassersteinDRO_StrongDuality_couplings

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Optimal transport cost** `W_c(P, Q) := inf_{γ ∈ Γ(P, Q)} E_γ[c(ξ, ξ')]`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), §2.2, eq. (3), p.5: the Wasserstein distance of order 1 is
`W(P, Q) := inf_{γ ∈ Γ(P,Q)} E_{((X̃,Z̃),(X,Z)) ∼ γ}[‖X̃ − X‖ + |Z̃ − Z|]`, where `Γ(P, Q)` is the set of
probability distributions on `(𝒳 × 𝒵)²` with marginals `P`, `Q` (p.6). This definition takes the
ground cost `c` as a parameter; the paper's cost is `fullCost` (and `inCost` on the in-sample
space).

**Formalization Note.** `Γ(P, Q)` is the published platform definition
`WassersteinDRO.StrongDuality.couplings` (a probability measure on the product with the two
push-forward marginals). The value lies in `ℝ≥0∞`; the ground costs used in this mission are
sums of distances, hence nonnegative, so `ENNReal.ofReal` loses nothing. The infimum over an empty
set of couplings would be `⊤`; for probability measures `P`, `Q` the product coupling exists. -/
noncomputable def transportCost {α : Type*} [MeasurableSpace α] (c : α → α → ℝ) (P Q : Measure α) :
    ℝ≥0∞ :=
  ⨅ γ ∈ WassersteinDRO.StrongDuality.couplings P Q, ∫⁻ q, ENNReal.ofReal (c q.1 q.2) ∂γ

end ShapleyNV


