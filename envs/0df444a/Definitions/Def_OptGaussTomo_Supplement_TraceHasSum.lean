-- Prove2me | Definitions.Def_OptGaussTomo_Supplement_TraceHasSum
-- name    : OptGaussTomo_Supplement_TraceHasSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:43:29.27629+00:00
-- url     : https://prove2.me/theorems/419c029a-acc3-406c-87eb-cfe0ab6c75df
-- title:
--   Convergence of an operator series in trace norm
-- statement:
--   For operators $T_k$ ($k\in K$, $K$ countable) and $S$ on $\ell^2(Y)$, the statement $S=\sum_kT_k$ **with convergence in trace norm** means: for every $\varepsilon>0$ there is a finite $F\subseteq K$ such that
--
--   $$
--   \Big\|S-\sum_{k\in F'}T_k\Big\|_1<\varepsilon\qquad\text{for every finite } F'\supseteq F .
--   $$
--
--   This is the sense of the sentence "The sums converge in trace norm" in Theorem E.1. When $K$ is finite it is the identity $S=\sum_kT_k$.
--
--   **Formalization Note** The trace norm is the published `traceSize`, which is $+\infty$ off the trace class, so the partial-sum errors are trace class. Convergence is over finite subsets (unconditional), matching sums indexed by an unordered collection.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Theorem E.1, p.64 ('The sums converge in trace norm')

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (traceSize)

namespace OptGaussTomo.Supplement

/-- **Convergence in trace norm** of a sum of operators (Chen, Fanizza, Girardi, Lami, Mele,
Walter, Witteveen, *Optimal tomography of bosonic and fermionic Gaussian states*,
arXiv:2607.11847, held version, sha256 0f7548a2…, Theorem E.1, p.64: "The sums converge in trace
norm"). `∑ₖ Tₖ = S` with the finite partial sums converging to `S` in trace norm along the directed
set of finite subsets of `K` (unconditional convergence; for finite `K` this is the equality
`∑ₖ Tₖ = S`). The trace norm is the published `traceSize`, which is `∞` off trace class. -/
def TraceHasSum {Y K : Type} (T : K → Matrix Y Y ℂ) (S : Matrix Y Y ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ F : Finset K, ∀ F' : Finset K, F ⊆ F' →
    traceSize (S - ∑ k ∈ F', T k) < ENNReal.ofReal ε

end OptGaussTomo.Supplement


