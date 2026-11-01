-- Prove2me | Definitions.Def_BayesClock_expectedAbove
-- name    : BayesClock_expectedAbove
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:16.851473+00:00
-- url     : https://prove2.me/theorems/784a5901-f26e-4f7e-935b-663938cfc7c2
-- title:
--   Expected number of bidders above a threshold
-- statement:
--   $\mu_S(t)=\mathbb E_v[|S(t,v)|]$ is the expected number of bidders of $S$ whose value exceeds $t$.
--
--   It is non-increasing in $t$, and equals $\sum_{i\in S}\Pr[v_i>t]$.
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, §3.2, p.7

import Mathlib
import Definitions.Def_BayesClock_aboveSet

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- `μ_S(t) = E_v[|S(t, v)|]`, the expected number of bidders of `S` above `t`.
Feldman et al., arXiv:2202.09291v1, §3.2, p.7.

**Formalization Note** It takes values in `ℝ≥0∞`, and for probability laws it equals
`∑ i ∈ S, ν i (Set.Ioi t)`, which is at most `|S|`. -/
noncomputable def expectedAbove {N : Type*} [Fintype N] (ν : N → Measure ℝ≥0) (S : Finset N)
    (t : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ v, ((aboveSet S t v).card : ℝ≥0∞) ∂Measure.pi ν

end BayesClock


