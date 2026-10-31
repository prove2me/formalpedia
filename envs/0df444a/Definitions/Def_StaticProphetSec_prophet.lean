-- Prove2me | Definitions.Def_StaticProphetSec_prophet
-- name    : StaticProphetSec_prophet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:59.477747+00:00
-- url     : https://prove2.me/theorems/6c19d2d3-8e90-456a-8baf-d79c46ca3819
-- title:
--   The prophet's value $\mathcal{PHT}_k(F)$
-- statement:
--   The **prophet's value** is the expected sum of the $k$ largest values:
--
--   $$\mathcal{PHT}_k(F)=\mathbb E\Big[\max_{S\subseteq[n],\ |S|\le k}\ \sum_{i\in S}V_i\Big].$$
--
--   **Formalization Note** On non-negative values the maximum over sets of at most $k$ applicants is the sum of the $k$ largest values (of all $n$ values when $n<k$). The value lies in $[0,\infty]$.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Definition 1, p.16

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace StaticProphetSec

/-- The prophet's value `PHT_k(F)`, "the expected sum of the k largest values" (Arnosti & Ma,
arXiv:2108.12893v2, Definition 1, p.16).

**Formalization Note.** On non-negative values the sum of the `k` largest values is the largest
sum over sets of at most `k` applicants; if `n < k` it is the sum of all `n` values. The index
type of the supremum is nonempty (it contains `∅`), and the supremum is taken in `ℝ≥0∞`, so it is
never a junk value. -/
noncomputable def prophet {n : ℕ} (k : ℕ) (μ : Fin n → Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ V, ⨆ S : {S : Finset (Fin n) // S.card ≤ k}, ∑ i ∈ S.1, ENNReal.ofReal (V i) ∂Measure.pi μ

end StaticProphetSec


