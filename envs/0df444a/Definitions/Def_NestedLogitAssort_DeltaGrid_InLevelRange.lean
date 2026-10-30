-- Prove2me | Definitions.Def_NestedLogitAssort_DeltaGrid_InLevelRange
-- name    : NestedLogitAssort_DeltaGrid_InLevelRange
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:07:36.755218+00:00
-- url     : https://prove2.me/theorems/7840f96d-f03d-486a-ab65-83133b7790e5
-- title:
--   Level range $l^L_i\le l\le l^U_i$ of a nest
-- statement:
--   Fix $\delta>1$ and a nest $i$, and let $v^L_i=v_{i0}+\min_{j\in N}v_{ij}$ and $v^U_i=v_{i0}+\sum_{j\in N}v_{ij}$. The paper sets $l^L_i=\min\{l\in\mathbb Z:\delta^l\ge v^L_i\}$ and $l^U_i=\min\{l\in\mathbb Z:\delta^l\ge v^U_i\}$ and uses the levels $l=l^L_i,\dots,l^U_i$. An integer $l$ is in range when
--
--   $$
--   \exists\,j\in N:\ v_{i0}+v_{ij}\le\delta^l\qquad\text{and}\qquad\delta^{l-1}<v_{i0}+\sum_{j\in N}v_{ij},
--   $$
--
--   that is, $\delta^l\ge v^L_i$ and $\delta^{l-1}<v^U_i$, the defining inequalities of the two minima.
--
--   **Formalization Note** Whenever $v^L_i>0$ this is exactly $l^L_i\le l\le l^U_i$. When $v^L_i=0$ (allowed on p. 7: $v_{i0}=0$ and a zero-weight product) the printed $l^L_i$ does not exist, since every $l$ has $\delta^l\ge0$; the predicate then admits every $l$ with $\delta^{l-1}<v^U_i$. When $v^U_i=0$, or $n=0$, no level is in range.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 6.2, pp. 27–28

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_Instance

namespace NestedLogitAssort.DeltaGrid

/-- **The level range `l ∈ {l^L_i, …, l^U_i}` of nest `i`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 6.2, pp. 27–28: with `v^L_i = v_{i0} + min_{j∈N} v_{ij}`,
`v^U_i = v_{i0} + ∑_{j∈N} v_{ij}`, `l^L_i = min{l ∈ ℤ : δ^l ≥ v^L_i}` and
`l^U_i = min{l ∈ ℤ : δ^l ≥ v^U_i}`, the levels used are `l = l^L_i, …, l^U_i`.

The predicate is the pair of defining inequalities of the two minima:
`l ≥ l^L_i ⟺ δ^l ≥ v^L_i ⟺ ∃ j, v_{i0} + v_{ij} ≤ δ^l`, and
`l ≤ l^U_i ⟺ δ^{l−1} < v^U_i`.

**Formalization Note.** For `δ > 1` and `v^L_i > 0` this is exactly `l^L_i ≤ l ≤ l^U_i`. When
`v^L_i = 0` (allowed on p. 7: `v_{i0} = 0` and a zero-weight product) the printed `l^L_i` is
undefined, since every `l` satisfies `δ^l ≥ 0`; the predicate then admits every `l` with
`δ^{l−1} < v^U_i`. When `v^U_i = 0`, or `n = 0`, no level is in range. `δ ^ l` is `zpow`. -/
def InLevelRange {M : Type*} {n : ℕ} (I : Instance M n) (δ : ℝ) (i : M) (l : ℤ) : Prop :=
  (∃ j : Fin n, I.w0 i + I.v i j ≤ δ ^ l) ∧ δ ^ (l - 1) < I.w0 i + ∑ j, I.v i j

end NestedLogitAssort.DeltaGrid


