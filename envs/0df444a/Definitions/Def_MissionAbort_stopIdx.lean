-- Prove2me | Definitions.Def_MissionAbort_stopIdx
-- name    : MissionAbort_stopIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:24.589465+00:00
-- url     : https://prove2.me/theorems/aca46e96-529b-4fcd-b10b-4904184d6008
-- title:
--   The stopping index
-- statement:
--   Along a signal path, with $\mathfrak T=\min\{n\delta:a_n(Y_{1:n})=1,\ n\in[N-1]\}\cup\{N\delta\}$, the index $\mathfrak T/\delta$.
--
--   **Formalization Note** The set contains $N$, so the minimum exists. The index set is $[N-1]$ in (7) too: the paper's "$n\in[N]$" there is a slip, since there is no rule $a_{\lambda,N}$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4, (1), p.11, and (7), p.15

import Mathlib
import Definitions.Def_MissionAbort_Rule

namespace MissionAbort

/-- The stopping index along a signal path (Sun, Hu & Ye, arXiv:2505.03225v1, §4, p.11): with
`𝔗 = min{nδ : aₙ(Y_{1:n}) = 1, n ∈ [N − 1]} ∪ {Nδ}`, this is `𝔗/δ`.

**Formalization Note.** `ys j` is the signal `Y_j`. The set contains `N`, so it is nonempty and the
natural-number `sInf` is its minimum. The stopping time is carried as an index, never as `𝔗/δ` in real
division. The set is over `n ∈ [N − 1]`, also in (7), where the page's "`n ∈ [N]`" is a slip. -/
noncomputable def stopIdx {K : ℕ} (N : ℕ) (a : Rule K) (ys : ℕ → Fin (K + 1)) : ℕ :=
  sInf ({n | 1 ≤ n ∧ n < N ∧ a n (fun i : Fin n => ys (i.val + 1)) = true} ∪ {N})

end MissionAbort


