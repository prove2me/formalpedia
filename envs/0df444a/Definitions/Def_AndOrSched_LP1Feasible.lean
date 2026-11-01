-- Prove2me | Definitions.Def_AndOrSched_LP1Feasible
-- name    : AndOrSched_LP1Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:15.770841+00:00
-- url     : https://prove2.me/theorems/5f25da4b-06bc-47c2-a7ab-3f1a414cd79b
-- title:
--   Feasible solutions of LP (1)
-- statement:
--   For a normalized instance with $p_j\in\{0,1\}$ and time slots $t\in[T]=\{1,\dots,T\}$, $x$ is feasible for LP (1) if
--   $$\sum_{t=1}^{T}x_{jt}=1\quad(j\in N),\qquad \sum_{j\in N}\sum_{s=t-p_j+1}^{t}x_{js}\le1\quad(t\in[T]),$$
--   $$\sum_{s=1}^{t+p_b}x_{bs}-\sum_{a\in\mathcal P(b)}\sum_{s=1}^{t}x_{as}\le0\quad(b\in B,\ \mathcal P(b)\ne\emptyset,\ t\in[T-p_b]),$$
--   $$\sum_{s=1}^{t+p_j}x_{js}-\sum_{s=1}^{t}x_{is}\le0\quad((i,j)\in E_\wedge,\ t\in[T-p_j]),\qquad x_{jt}\ge0 .$$
--   These are constraints (1b)–(1f). The ranges of (1d) and (1e) are exactly as printed.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.7, LP (1), (1b)–(1f)

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_andRel
import Definitions.Def_AndOrSched_orPred
import Definitions.Def_AndOrSched_cum
import Definitions.Def_AndOrSched_pN
import Definitions.Def_AndOrSched_horizon
open scoped Classical NNReal

namespace AndOrSched

/-- Feasibility for the time-indexed LP (1) (Happach, Schulz, arXiv:2001.07011v1, §2, p.7), with time slots `t ∈ [T] = {1,…,T}`:
* (1b) `Σ_{t=1}^{T} x_{jt} = 1` for all `j ∈ N`;
* (1c) `Σ_{j∈N} Σ_{s=t−pⱼ+1}^{t} x_{js} ≤ 1` for all `t ∈ [T]`;
* (1d) `Σ_{s=1}^{t+p_b} x_{bs} − Σ_{a∈𝒫(b)} Σ_{s=1}^{t} x_{as} ≤ 0` for all `b ∈ B` with
  `𝒫(b) ≠ ∅` and all `t ∈ [T − p_b]`;
* (1e) `Σ_{s=1}^{t+pⱼ} x_{js} − Σ_{s=1}^{t} x_{is} ≤ 0` for all `(i, j) ∈ E∧` and all `t ∈ [T − pⱼ]`;
* (1f) `x_{jt} ≥ 0` for all `j ∈ N`, `t ∈ [T]`.

**Formalization Note** `x : N → ℕ → ℝ`; only the values at slots `1, …, T` enter the constraints,
the objective and the `α`-points. The LP is meant for normalized instances with processing times
in `{0, 1}` (`pN` reads the integer processing time). The sum `Σ_{s=t−pⱼ+1}^{t}` is over
`s ∈ (t − pⱼ, t]`. The ranges `[T − p_b]` and `[T − pⱼ]` of (1d) and (1e) are as printed. -/
def LP1Feasible (I : Instance) (x : I.N → ℕ → ℝ) : Prop :=
  (∀ j, cum x j (horizon I) = 1) ∧
  (∀ t ∈ Finset.Icc 1 (horizon I), ∑ j, ∑ s ∈ Finset.Ioc (t - pN I j) t, x j s ≤ 1) ∧
  (∀ b, (orPred I b).Nonempty → ∀ t ∈ Finset.Icc 1 (horizon I - pN I (Sum.inr b)),
    cum x (Sum.inr b) (t + pN I (Sum.inr b)) - ∑ a ∈ orPred I b, cum x (Sum.inl a) t ≤ 0) ∧
  (∀ i j, andRel I i j → ∀ t ∈ Finset.Icc 1 (horizon I - pN I j),
    cum x j (t + pN I j) - cum x i t ≤ 0) ∧
  (∀ j, ∀ t ∈ Finset.Icc 1 (horizon I), 0 ≤ x j t)

end AndOrSched


