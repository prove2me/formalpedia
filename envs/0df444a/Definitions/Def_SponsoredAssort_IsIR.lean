-- Prove2me | Definitions.Def_SponsoredAssort_IsIR
-- name    : SponsoredAssort_IsIR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:53.893076+00:00
-- url     : https://prove2.me/theorems/925a87e4-7ef5-4b4f-9a4a-3818100d2100
-- title:
--   Ex-post individual rationality (IR)
-- statement:
--   A mechanism is **ex-post individually rational** if truthful participation never gives negative utility:
--
--   $$
--   u_i(v_i,v)\ \ge\ 0\qquad\text{for all sellers }i\text{ and all }v\in\mathbb R^n_+ .
--   $$
--
--   The set $M$ of the paper is the set of deterministic mechanisms that satisfy (IC) and (IR).
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), §2, (IR), p.11

import Mathlib
import Definitions.Def_SponsoredAssort_utility

open scoped NNReal

namespace SponsoredAssort

/-- **Ex-post individual rationality (IR)** (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022),
§2, p.11): `uᵢ(vᵢ, v) ≥ 0` for every seller `i` and every profile `v ∈ ℝⁿ₊`. -/
def IsIR {n : ℕ} (r : Fin n → ℝ) (m : Mechanism n) : Prop :=
  ∀ (i : Fin n) (v : Attr n), 0 ≤ utility r m i (v i) v

end SponsoredAssort


