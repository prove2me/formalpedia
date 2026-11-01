-- Prove2me | Definitions.Def_SponsoredAssort_Mechanism
-- name    : SponsoredAssort_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:49.005689+00:00
-- url     : https://prove2.me/theorems/b768154d-08d9-42ff-9db9-b929afb25ffa
-- title:
--   Deterministic mechanism $m=(S(\cdot),p(\cdot))$
-- statement:
--   A **deterministic (direct) mechanism** consists of
--
--   1. an allocation rule $S:\mathbb R^n_+\to 2^{[n]}$, where $S(\hat v)$ is the assortment displayed when the sellers report $\hat v$, and
--   2. a payment rule $p:\mathbb R^n_+\to\mathbb R^n$, where $p_i(\hat v)$ is the side-payment of seller $i$.
--
--   **Formalization Note** Payments are real-valued as in the paper's $p:\mathbb R^n_+\to\mathbb R^n$, and no measurability is imposed on either rule.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), §2, p.10

import Mathlib
import Definitions.Def_SponsoredAssort_Attr

open scoped NNReal

namespace SponsoredAssort

/-- A **deterministic mechanism** `m = (S(·), p(·))` (Balseiro, Désir, SSRN 3821382
(Feb. 21, 2022), §2, p.10): an allocation rule `S : ℝⁿ₊ → 𝒮 = 2^[n]` and a payment rule
`p : ℝⁿ₊ → ℝⁿ`; `S(v̂)` is the assortment displayed and `pᵢ(v̂)` the side-payment of seller `i`
when the sellers report `v̂`.

**Formalization Note.** No measurability is required of either rule, and payments are
real-valued, as in the paper's `p : ℝⁿ₊ → ℝⁿ` (p.10). -/
structure Mechanism (n : ℕ) where
  /-- The allocation rule `S(v̂)`. -/
  alloc : Attr n → Finset (Fin n)
  /-- The payment rule: `pay v̂ i = pᵢ(v̂)`. -/
  pay : Attr n → Fin n → ℝ

end SponsoredAssort


