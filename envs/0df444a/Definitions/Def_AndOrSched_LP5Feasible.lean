-- Prove2me | Definitions.Def_AndOrSched_LP5Feasible
-- name    : AndOrSched_LP5Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:47.326928+00:00
-- url     : https://prove2.me/theorems/b056b96e-02c4-4579-b6ca-fd74dad610c7
-- title:
--   Feasible solutions of LP (5) (corrected (5f))
-- statement:
--   For a normalized instance, $\varepsilon'>0$ and intervals $l\in[L]$, $x$ is feasible for LP (5) if
--   $$\sum_{l=1}^{L}x_{jl}=1,\qquad \sum_{j\in N}\sum_{k=1}^{l}p_jx_{jk}\le\tau_l,\qquad \sum_{k=1}^{l}x_{bk}-\sum_{a\in\mathcal P(b)}\sum_{k=1}^{l}x_{ak}\le0,\qquad \sum_{k=1}^{l}x_{jk}-\sum_{k=1}^{l}x_{ik}\le0,$$
--   for all $j$, $l$, all $b$ with $\mathcal P(b)\ne\emptyset$ and all $(i,j)\in E_\wedge$; and $x_{jl}\ge0$, with $x_{jl}=0$ whenever $\tau_l<p_j$.
--
--   The last condition corrects the printed (5f), which keeps $x_{jl}$ only when $\tau_{l-1}\ge p_j$: as printed, the LP is infeasible for $A=\{a\}$, $B=\{b\}$, $p_a=2$, $p_b=0$, $\mathcal P(b)=\{a\}$, $\varepsilon'=1/2$ (then $\tau=(1,1,1.5,2.25)$, $L=3$, no $l$ has $\tau_{l-1}\ge2$), although the instance has a feasible schedule. A job completing in $(\tau_{l-1},\tau_l]$ has $p_j\le C_j\le\tau_l$, so the corrected condition is valid for schedules.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.9, LP (5), (5b)–(5f)

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_andRel
import Definitions.Def_AndOrSched_orPred
import Definitions.Def_AndOrSched_cum
import Definitions.Def_AndOrSched_pN
import Definitions.Def_AndOrSched_numIntervals
import Definitions.Def_AndOrSched_tau
open scoped Classical NNReal

namespace AndOrSched

/-- Feasibility for the interval-indexed LP (5) (Happach, Schulz, arXiv:2001.07011v1, §2, p.9), with intervals `l ∈ [L]`:
* (5b) `Σ_{l=1}^{L} x_{jl} = 1` for all `j ∈ N`;
* (5c) `Σ_{j∈N} Σ_{k=1}^{l} pⱼ x_{jk} ≤ τ_l` for all `l ∈ [L]`;
* (5d) `Σ_{k=1}^{l} x_{bk} − Σ_{a∈𝒫(b)} Σ_{k=1}^{l} x_{ak} ≤ 0` for all `b ∈ B` with `𝒫(b) ≠ ∅`,
  `l ∈ [L]`;
* (5e) `Σ_{k=1}^{l} x_{jk} − Σ_{k=1}^{l} x_{ik} ≤ 0` for all `(i, j) ∈ E∧`, `l ∈ [L]`;
* (5f), corrected: `x_{jl} ≥ 0` for all `j`, `l ∈ [L]`, and `x_{jl} = 0` when `τ_l < pⱼ`.

**Formalization Note** The printed (5f) declares the variable `x_{jl}` only when `τ_{l−1} ≥ pⱼ`.
That makes LP (5) infeasible for `A = {a}`, `B = {b}`, `p_a = 2`, `p_b = 0`, `𝒫(b) = {a}`,
`ε' = 1/2` (then `τ = (1, 1, 1.5, 2.25)`, `L = 3`, and no `l` has `τ_{l−1} ≥ 2`, so (5b) fails
for `a`), although the instance has a feasible schedule. The condition is corrected to `τ_l ≥ pⱼ`
(a job completing in `(τ_{l−1}, τ_l]` has `pⱼ ≤ Cⱼ ≤ τ_l`). The LP is meant for normalized
instances with integer processing times (`pN`). -/
def LP5Feasible (I : Instance) (ε' : ℝ) (x : I.N → ℕ → ℝ) : Prop :=
  (∀ j, cum x j (numIntervals I ε') = 1) ∧
  (∀ l ∈ Finset.Icc 1 (numIntervals I ε'),
    ∑ j, ∑ k ∈ Finset.Icc 1 l, (pN I j : ℝ) * x j k ≤ tau ε' l) ∧
  (∀ b, (orPred I b).Nonempty → ∀ l ∈ Finset.Icc 1 (numIntervals I ε'),
    cum x (Sum.inr b) l - ∑ a ∈ orPred I b, cum x (Sum.inl a) l ≤ 0) ∧
  (∀ i j, andRel I i j → ∀ l ∈ Finset.Icc 1 (numIntervals I ε'), cum x j l - cum x i l ≤ 0) ∧
  (∀ j, ∀ l ∈ Finset.Icc 1 (numIntervals I ε'),
    0 ≤ x j l ∧ (tau ε' l < (pN I j : ℝ) → x j l = 0))

end AndOrSched


