-- Prove2me | Definitions.Def_CoCoNet_bankrupt
-- name    : CoCoNet_bankrupt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:17.849994+00:00
-- url     : https://prove2.me/theorems/1f8c77bf-94c7-4cfc-a7c5-66cc9b01d2c5
-- title:
--   Bankrupt banks read off a price vector: $\{i : s_i<0\}$
-- statement:
--   For a vector of stock prices $s\in\mathbb R^n$, the set of **bankrupt** banks is
--   $$B(s)=\{i\in[n] : s_i<0\}.$$
--   In an equilibrium the bankrupt banks must be exactly these (consistency condition, p.9).
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, §2 'Equilibrium Concept', p.9

import Mathlib

namespace CoCoNet

/-- **The bankrupt banks read off a price vector**, `B = {i | sᵢ < 0}`.
Balter, Schweizer & Vera, arXiv:2011.06474v1, §2 "Equilibrium Concept", p.9: "In equilibrium, we
must have B = {i|sᵢ < 0}, C = {i|0 ≤ sᵢ ≤ lᵢ} and H = {i|sᵢ > lᵢ}." -/
noncomputable def bankrupt {n : ℕ} (s : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => s i < 0

end CoCoNet


