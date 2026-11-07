-- Prove2me | Definitions.Def_SparseHistComm_IsAccurate
-- name    : SparseHistComm_IsAccurate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:39:21.311954+00:00
-- url     : https://prove2.me/theorems/dc64706a-b14a-4d48-ab32-cc8091702ace
-- title:
--   $(D,\delta)$-accurate protocol
-- statement:
--   A protocol is **$(D,\delta)$-accurate** for $k$-sparse inputs if
--   $$
--   \inf_{\substack{x_1,\dots,x_n \in \{0,1\}^d \\ \|x_i\|_0 \le k\ \forall i}} P(\|\hat u - u\|_1 \le D) \ \ge\ 1 - \delta ,
--   $$
--   that is, on every admissible input profile the estimate is within $\ell_1$ distance $D$ of the empirical histogram with probability at least $1-\delta$. The guarantee is minimax over all inputs, including every pattern of support overlap.
--
--   **Formalization Note** The infimum bound is written as a bound for every admissible profile. The ranges $0 \le D < k$ and $0 \le \delta < 1$ of Definition 1 are hypotheses of the theorems that use the predicate.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Definition 1, (2), p.2

import Mathlib
import Definitions.Def_SparseHistComm_succProb
import Definitions.Def_SparseHistComm_Admissible
open scoped ENNReal

namespace SparseHistComm

/-- A protocol is **`(D, δ)`-accurate** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Definition 1, (2), p.2) if
`inf_{x₁,…,xₙ ∈ {0,1}^d, ‖xᵢ‖₀ ≤ k ∀i} P(‖û − u‖₁ ≤ D) ≥ 1 − δ`, i.e. the success probability is at
least `1 − δ` on every admissible input profile.

**Formalization Note** The infimum bound is stated as a bound for every admissible profile (the
two are equivalent). The ranges `0 ≤ D < k`, `0 ≤ δ < 1` of Definition 1 are hypotheses of the
theorems, not part of this predicate. -/
def IsAccurate {n d : ℕ} (P : Protocol n d) (k : ℕ) (D δ : ℝ) : Prop :=
  ∀ x : Fin n → Finset (Fin d), Admissible k x → ENNReal.ofReal (1 - δ) ≤ succProb P D x

end SparseHistComm


