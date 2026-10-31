-- Prove2me | Definitions.Def_CoCoNet_healthy
-- name    : CoCoNet_healthy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:17.151168+00:00
-- url     : https://prove2.me/theorems/829fb405-8aae-484e-96f3-6de4312085dd
-- title:
--   Healthy banks read off a price vector: $\{i : s_i>l_i\}$
-- statement:
--   For stock prices $s\in\mathbb R^n$ and conversion thresholds $l\in\mathbb R^n$, the set of **healthy** banks is
--   $$H(s)=\{i\in[n] : s_i>l_i\}$$
--   (strict inequality). Healthy banks pay back their convertible debt. When $l\ge 0$ the three sets $B(s)$, $C(s)$, $H(s)$ form a partition of $[n]$.
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, §2 'Equilibrium Concept', p.9

import Mathlib

namespace CoCoNet

/-- **The healthy banks read off a price vector**, `H = {i | sᵢ > lᵢ}` (strict).
Balter, Schweizer & Vera, arXiv:2011.06474v1, §2 "Equilibrium Concept", p.9: "In equilibrium, we
must have B = {i|sᵢ < 0}, C = {i|0 ≤ sᵢ ≤ lᵢ} and H = {i|sᵢ > lᵢ}."
`l` is the vector of conversion thresholds.

**Formalization Note.** When `0 ≤ l`, `bankrupt s`, `converting l s`, `healthy l s` partition
`Fin n` (the paper's sets `S_{B,C,H}` partition ℝⁿ, p.12). -/
noncomputable def healthy {n : ℕ} (l s : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => l i < s i

end CoCoNet


