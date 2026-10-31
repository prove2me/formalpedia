-- Prove2me | Definitions.Def_CoCoNet_converting
-- name    : CoCoNet_converting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:19.887252+00:00
-- url     : https://prove2.me/theorems/e392ac89-4af9-4d0b-8f7c-7a9a82727925
-- title:
--   Converting banks read off a price vector: $\{i : 0\le s_i\le l_i\}$
-- statement:
--   For stock prices $s\in\mathbb R^n$ and conversion thresholds $l\in\mathbb R^n$, the set of **converting** banks is
--   $$C(s)=\{i\in[n] : 0\le s_i\le l_i\}.$$
--   Both inequalities are weak: a bank whose price equals its threshold converts. In an equilibrium the converting banks must be exactly these (p.9).
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, §2 'Equilibrium Concept', p.9

import Mathlib

namespace CoCoNet

/-- **The converting banks read off a price vector**, `C = {i | 0 ≤ sᵢ ≤ lᵢ}` (closed at both
ends).
Balter, Schweizer & Vera, arXiv:2011.06474v1, §2 "Equilibrium Concept", p.9: "In equilibrium, we
must have B = {i|sᵢ < 0}, C = {i|0 ≤ sᵢ ≤ lᵢ} and H = {i|sᵢ > lᵢ}."
`l` is the vector of conversion thresholds. -/
noncomputable def converting {n : ℕ} (l s : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => 0 ≤ s i ∧ s i ≤ l i

end CoCoNet


