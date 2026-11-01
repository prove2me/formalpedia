-- Prove2me | Definitions.Def_SponsoredAssort_Attr
-- name    : SponsoredAssort_Attr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:06.137988+00:00
-- url     : https://prove2.me/theorems/76c6cdcd-d5c5-4386-b54b-8aca0116297c
-- title:
--   Attractiveness profiles $v\in\mathbb R^n_+$
-- statement:
--   There are $n$ sellers. Seller $i$'s product has an **attractiveness** $v_i\ge0$, the exponential of the consumer's mean utility for it, which is private information of seller $i$. An attractiveness profile is a vector
--
--   $$
--   v=(v_1,\dots,v_n)\in\mathbb R^n_+ .
--   $$
--
--   Priors $F\in\mathcal P(\mathbb R^n_+)$ are probability measures on this space and may be arbitrarily correlated across sellers.
--
--   **Formalization Note** Sellers are indexed by `Fin n`, so Lean's seller $i$ is the paper's seller $i+1$. Profiles are functions `Fin n → ℝ≥0` with the product Borel σ-algebra.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), §2, p.9

import Mathlib

open scoped NNReal

namespace SponsoredAssort

/-- An **attractiveness profile** `v ∈ ℝⁿ₊` of the `n` sellers (Balseiro, Désir,
*Incentive-Compatible Assortment Optimization for Sponsored Products*, SSRN 3821382 (Feb. 21,
2022), §2, p.9): seller `i` has attractiveness `vᵢ ≥ 0`, which is its private information.

**Formalization Note.** Sellers are `Fin n`, so the Lean index `i` is the paper's seller `i + 1`.
Attractiveness values are nonnegative reals `ℝ≥0`. The type carries Mathlib's product Borel
σ-algebra, on which the priors `F ∈ P(ℝⁿ₊)` live. -/
abbrev Attr (n : ℕ) : Type := Fin n → ℝ≥0

end SponsoredAssort


