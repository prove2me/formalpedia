-- Prove2me | Definitions.Def_MNLStability_expX
-- name    : MNLStability_expX
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:53.923124+00:00
-- url     : https://prove2.me/theorems/3bdace29-bdcf-474c-b685-213ff31e0261
-- title:
--   Expected demand $\mathbb E[X_i^U]$ and expected revenue $\mathbb E[R(U)]$
-- statement:
--   1. $\mathbb E[X_i^U(m)]$ is the expected number of units of product $i$ consumed by $m$ customers from the initial vector $U$.
--   2. $\mathbb E[X_i^U]=\sum_m p_M(m)\,\mathbb E[X_i^U(m)]$ is the same expectation when the number of customers has law $p_M$.
--   3. The **expected revenue** of $U$ is
--   $$\mathbb E[R(U)]=\sum_{i\in[n]}r_i\,\mathbb E[X_i^U].$$
--
--   The revenue of a sample path is $\sum_i r_iX_i^U$, so item 3 is the expected revenue by linearity; it is the identity the paper uses in the proof of Lemma 3.
--
--   **Formalization Note** The expectation in item 1 is a sum over all outcomes in $[0,\infty]$, so no summability side condition arises; it is at most $U_i$, so the conversion to a real number is exact.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §1.1, p.4; §2.1, p.10; proof of Lemma 3, p.15

import Mathlib
import Definitions.Def_MNLStability_demand

open scoped ENNReal

namespace MNLStability

variable {n : ℕ}

/-- `E[X_i^U(m)]`, the expected number of units of product `i` consumed by `m` customers from the
initial inventory vector `U` (SSRN:3498325, §5.1, p.25).

**Formalization Note.** The expectation is an `ℝ≥0∞` sum over the whole (countable) outcome space,
so no summability side condition is needed; it is at most `U i`, hence finite, and `toReal` is
exact. -/
noncomputable def expXm (wts : Weights n) (U : Fin n → ℕ) (m : ℕ) (i : Fin n) : ℝ :=
  (∑' x, demand wts U m x * ((x.1 i : ℕ) : ℝ≥0∞)).toReal

/-- `E[X_i^U]`, the expected number of units of product `i` consumed when the inventory vector `U`
is stocked and the number of customers `M` has law `pM` (§2.1, p.10). -/
noncomputable def expX (wts : Weights n) (pM : ℕ →₀ ℝ) (U : Fin n → ℕ) (i : Fin n) : ℝ :=
  ∑ m ∈ pM.support, pM m * expXm wts U m i

/-- `E[R(U)] = Σ_i r_i · E[X_i^U]`, the expected revenue of the inventory vector `U` (§1.1, p.4;
the identity is used in the proof of Lemma 3, p.15).

**Formalization Note.** The revenue of a sample path is `Σ_i r_i X_i`, so this is the definition of
the expected revenue, by linearity of expectation. -/
noncomputable def expR (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (U : Fin n → ℕ) : ℝ :=
  ∑ i, r i * expX wts pM U i

end MNLStability


