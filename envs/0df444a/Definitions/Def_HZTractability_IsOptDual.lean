-- Prove2me | Definitions.Def_HZTractability_IsOptDual
-- name    : HZTractability_IsOptDual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:07:16.371356+00:00
-- url     : https://prove2.me/theorems/c0302ad3-877d-4b58-88bd-22c33ad2ba34
-- title:
--   Optimal demand dual $(\beta_i,\mu_i)$
-- statement:
--   The dual of buyer $i$'s demand problem (OptBundle) is
--   $$
--   V_i(p)=\min_{\beta_i,\mu_i}\ \beta_i+\mu_i\quad\text{subject to}\quad \beta_i p_j+\mu_i\ge u_{ij}\ \text{for every } j,\quad \beta_i\ge 0,\quad \mu_i\in\mathbb R .
--   $$
--   A pair $(\beta,\mu)$ is an **optimal demand dual** of buyer $i$ at prices $p$ if $\beta\ge 0$, $\beta p_j+\mu\ge u_{ij}$ for every good $j$, and $\beta+\mu=V_i(p)$. Here $\beta$ is the budget multiplier and $\mu$ the quantity multiplier; $\beta p_j+\mu-u_{ij}$ is the **reduced slack** of good $j$.
--
--   Optimal duals are the main tool of the demand estimates of Appendix B.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), (Dual), Lemma 2.4, p.8 (PDF p.10); Lemma B.1, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_HZTractability_IsUnitBundle

namespace HZTractability

/-- **An optimal demand dual** `(β_i, μ_i)` of buyer `i` (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, (Dual), Lemma 2.4, p.8 (PDF 10), and Lemma B.1,
p.38 (PDF 40): "β_i ≥ 0, β_i p_j + μ_i ≥ u_ij, β_i + μ_i = V_i(p)").

`β` is the budget multiplier and `μ` the quantity multiplier of (OptBundle); the pair is dual
feasible (`β ≥ 0` and `β p_j + μ ≥ u_ij` for every good `j`) and its objective `β + μ` equals the
budget-one optimal utility `V_i(p)` (`IsOptValue`).

**Formalization Note** `μ` is an unrestricted real, as in (Dual). -/
def IsOptDual {B G : Type} [Fintype G] (u : B → G → ℝ) (p : G → ℝ) (i : B) (β μ : ℝ) : Prop :=
  0 ≤ β ∧ (∀ j, u i j ≤ β * p j + μ) ∧ IsOptValue u p i (β + μ)

end HZTractability


