-- Prove2me | Definitions.Def_StaticProphetSec_lpValue
-- name    : StaticProphetSec_lpValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:06.048152+00:00
-- url     : https://prove2.me/theorems/c5b73a6e-b1e9-40ef-b610-4727c2814d4f
-- title:
--   The LP relaxation (ex-ante value) $\mathcal{LP}_k(F)$
-- statement:
--   The **LP relaxation**, or **ex-ante value**, is
--
--   $$\mathcal{LP}_k(F)=\sup\Big\{\sum_{i=1}^n\int_{1-x_i}^1F_i^{-1}(z)\,dz\ :\ \sum_{i=1}^nx_i\le k;\ 0\le x_i\le1\ \forall i\Big\}.$$
--
--   Here $x_i$ is the probability of accepting $i$, the constraint that at most $k$ applicants are accepted holds only in expectation, and $i$ is accepted whenever it takes a value in its top $x_i$-th quantile.
--
--   **Formalization Note** The paper prints $x_i\ge0$; the bound $x_i\le1$ is added because $F_i^{-1}(z)$ is undefined for $z<0$ and $x_i$ is a probability. $F_i^{-1}$ is the published `quantileFunction`, integrated over the open interval $(1-x_i,1)$, on which it is finite. The supremum lies in $[0,\infty]$.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Definition 1, p.16

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction

open MeasureTheory
open scoped ENNReal
open RiskFunctionals.StochDominance (quantileFunction)

namespace StaticProphetSec

/-- The LP relaxation (ex-ante value) `LP_k(F) = sup { ∑ i, ∫_{1-x_i}^1 F_i⁻¹(z) dz :
∑ i, x_i ≤ k; 0 ≤ x_i ≤ 1 }` (Arnosti & Ma, arXiv:2108.12893v2, Definition 1, p.16).

**Formalization Note.** The paper prints `x_i ≥ 0`; here also `x_i ≤ 1`, because the same page
says "x_i denotes the probability of accepting i" and `F_i⁻¹(z)` is undefined for `z < 0`. The
integral is over the open interval `(1 - x_i, 1)`, on which `quantileFunction` is the paper's
`F_i⁻¹` and is finite; the endpoints are null. Values lie in `ℝ≥0∞` (non-negative for an instance
with `μ i (Set.Iio 0) = 0`), so the supremum is in `ℝ≥0∞` and may be `∞`. -/
noncomputable def lpValue {n : ℕ} (k : ℕ) (μ : Fin n → Measure ℝ) : ℝ≥0∞ :=
  ⨆ x : Fin n → ℝ, ⨆ _ : (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i ≤ (k : ℝ),
    ∑ i, ∫⁻ z in Set.Ioo (1 - x i) 1, ENNReal.ofReal (quantileFunction (μ i) z)

end StaticProphetSec


