-- Prove2me | Definitions.Def_SponsoredAssort_IsIC
-- name    : SponsoredAssort_IsIC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:58.969037+00:00
-- url     : https://prove2.me/theorems/071a53e9-1af6-431a-92c2-7a771fb03ef7
-- title:
--   Ex-post incentive compatibility (IC)
-- statement:
--   A mechanism is **ex-post incentive compatible** if truthful reporting is a best response for every seller whatever the others' attractiveness:
--
--   $$
--   u_i(v_i,v)\ \ge\ u_i(\hat v_i,v)\qquad\text{for all sellers }i,\ \text{all reports }\hat v_i\ge0,\ \text{all }v\in\mathbb R^n_+ .
--   $$
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), §2, (IC), p.11

import Mathlib
import Definitions.Def_SponsoredAssort_utility

open scoped NNReal

namespace SponsoredAssort

/-- **Ex-post incentive compatibility (IC)** (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022),
§2, p.11): `uᵢ(vᵢ, v) ≥ uᵢ(v̂ᵢ, v)` for every seller `i`, every report `v̂ᵢ ≥ 0` and every
profile `v ∈ ℝⁿ₊`. -/
def IsIC {n : ℕ} (r : Fin n → ℝ) (m : Mechanism n) : Prop :=
  ∀ (i : Fin n) (v : Attr n) (y : ℝ≥0), utility r m i y v ≤ utility r m i (v i) v

end SponsoredAssort


