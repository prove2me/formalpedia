-- Prove2me | Definitions.Def_SmoothedNash_Supplement_alg3Time
-- name    : SmoothedNash_Supplement_alg3Time
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:01:55.972029+00:00
-- url     : https://prove2.me/theorems/be1d0761-c65d-4de3-9703-fcac0b5e415f
-- title:
--   Running time of Algorithm 3 in the cost model of Remark 3.5
-- statement:
--   The running time of Algorithm 3 charges, for every level $k = 1, \dots, K$ and every parent $x \in D_{k-1}$, the enumeration of $C(x,k)$ (the prefix count of Remark 3.5) plus $(n+1)^\kappa$ for every candidate $y \in C(x,k)$, which pays for the evaluation of $F(y)$, the norm test and the dictionary insertion into $D_k$:
--   $$
--   \mathrm{time}_\kappa = \sum_{k=1}^K \sum_{x \in D_{k-1}} \Bigl( \mathrm{enum}(n) + (n+1)^\kappa |C(x,k)| \Bigr).
--   $$
--
--   **Formalization Note** The paper's "poly($n$) per insertion" is unspecified; the theorem quantifies over every exponent $\kappa$. No constant setup cost is charged.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Remark 3.5, pp.22–23

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_alg3Candidates
import Definitions.Def_SmoothedNash_Supplement_alg3Level
import Definitions.Def_SmoothedNash_Supplement_alg3Depth
import Definitions.Def_SmoothedNash_Supplement_alg3EnumCost
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The running time of Algorithm 3 in the cost model of Remark 3.5 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), pp.22–23): for each
level `k = 1, …, K` and each parent `x ∈ D_{k−1}`, the enumeration of `C(x, k)` (`alg3EnumCost n`
steps) plus `(n + 1)^κ` per candidate `y ∈ C(x, k)` for its evaluation of `F`, the norm test and the
dictionary insertion into `D_k` ("poly(n) per insertion").

**Formalization Note** The paper leaves the polynomial per-candidate overhead unspecified; the theorem
is quantified over every exponent `κ`. No constant setup or output cost is charged. -/
noncomputable def alg3Time (κ : ℕ) {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (L1 ε : ℝ) : ℕ :=
  ∑ k ∈ Finset.range (alg3Depth L1 ε), ∑ i ∈ alg3Level F L1 k,
    (alg3EnumCost n + (n + 1) ^ κ * (alg3Candidates n (k + 1) i).card)

end SmoothedNash.Supplement


