-- Prove2me | Definitions.Def_DeltaSLearning_cycleLength
-- name    : DeltaSLearning_cycleLength
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:42.406991+00:00
-- url     : https://prove2.me/theorems/fae4fcc6-199e-4a81-a461-b33e26e7e442
-- title:
--   Cycle length $L(\delta)$
-- statement:
--   For a demand path $d_0,d_1,\dots$ and a gap $\delta$, the cycle length is the hitting time
--   $$L(\delta) := \min\{k\ge1:\ d_0+\dots+d_{k-1}\ge\delta\},$$
--   the number of periods of one cycle of a $(\delta,S)$ policy started at level $S$: the policy reorders once the cumulative demand of the cycle reaches the gap $\delta$. It does not depend on $S$.
--
--   **Formalization Note** The demands of the cycle are 0-based. The minimum is over $k\ge1$, which equals Lemma 2's $\min\{t: W_t\ge\delta\}$ for $\delta>0$ and gives one period at $\delta=0$. If the partial sums never reach $\delta$, the value is the junk $0$ ($\inf\emptyset$ on $\mathbb N$); under Assumption 1 this happens only on a null set.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), §3, p.10; Lemma 2, p.12; eq. (48), p.37

import Mathlib

namespace DeltaSLearning

/-- The length `L(δ)` of a cycle of a `(δ, S)` policy driven by the demands `d 0, d 1, …`
of the cycle: the first `k ≥ 1` with `d 0 + ⋯ + d (k - 1) ≥ δ`. It does not depend on `S`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), §3 p.10 ("L(δ,S) is, in fact, independent of S"), Lemma 2 p.12, eq. (48) p.37.

**Formalization Note** Demands are 0-based: `d k` is the demand of the cycle's `(k+1)`-st
period. The hitting time is over `k ≥ 1`, which equals Lemma 2's `min{t : W_t ≥ δ}` for
`δ > 0` and is `1` at `δ = 0` (a cycle has at least one period). If the partial sums never
reach `δ` the value is the junk `sInf ∅ = 0`; under Assumption 1 this happens only on a null
set. -/
noncomputable def cycleLength (δ : ℝ) (d : ℕ → ℝ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ δ ≤ ∑ i ∈ Finset.range k, d i}

end DeltaSLearning


