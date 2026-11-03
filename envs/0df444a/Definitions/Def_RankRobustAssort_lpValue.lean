-- Prove2me | Definitions.Def_RankRobustAssort_lpValue
-- name    : RankRobustAssort_lpValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:01.523178+00:00
-- url     : https://prove2.me/theorems/865230bf-01a4-4330-8d16-afcfc9dbe1b5
-- title:
--   Optimal value of the linear program (2)
-- statement:
--   For an assortment $S$, this is the optimal objective value of the linear optimization problem
--
--   $$
--   \begin{aligned}
--   \min_{\lambda,\epsilon}\quad & \sum_{(i_1,\dots,i_M)\in\mathcal L}\rho_{i_1\cdots i_M}(S)\,\lambda_{i_1\cdots i_M}\\
--   \text{s.t.}\quad & \sum_{(i_1,\dots,i_M)\in\mathcal L:\ i_m=i}\lambda_{i_1\cdots i_M}-\epsilon_{m,i}=v_{m,i}\quad \forall m\in\mathcal M,\ i\in S_m,\\
--   & \sum_{(i_1,\dots,i_M)\in\mathcal L}\lambda_{i_1\cdots i_M}=1,\qquad \|\epsilon\|\le\eta,\\
--   & \lambda_{i_1\cdots i_M}\ge0\quad\forall (i_1,\dots,i_M)\in\mathcal L.
--   \end{aligned}\tag{2}
--   $$
--
--   The assortment $S$ appears only in the objective, not in the constraints (Remark 1).
--
--   **Formalization Note.** The weights are a function on all tuples, of which only the entries indexed by $\mathcal L$ enter the program. The coefficient $\rho_{i_1\cdots i_M}(S)$ is converted to a real number with default $0$ for the value $+\infty$; for $S\in\mathcal S$ and tuples in $\mathcal L$ it is finite, so the default never occurs where the paper uses (2). The optimal value is the infimum of the objective over the feasible set; the objective is bounded below by $0$ and the infimum is attained when (2) is feasible.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Proposition 1, (2), p.15

import Mathlib
import Definitions.Def_RankRobustAssort_errNorm
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_rho

open Classical

namespace RankRobustAssort

/-- The optimal objective value of the linear optimization problem (2) for an assortment `S`:

minimize over `λ, ϵ`  `∑_{(i₁,…,i_M)∈ℒ} ρ_{i₁⋯i_M}(S) λ_{i₁⋯i_M}`
subject to `∑_{(i₁,…,i_M)∈ℒ : i_m = i} λ_{i₁⋯i_M} − ϵ_{m,i} = v_{m,i}` for all `m ∈ ℳ, i ∈ S_m`,
`∑_{(i₁,…,i_M)∈ℒ} λ_{i₁⋯i_M} = 1`, `‖ϵ‖ ≤ η`, `λ_{i₁⋯i_M} ≥ 0` for all `(i₁,…,i_M) ∈ ℒ`.

Sturt, arXiv:2112.05010v4, Proposition 1, (2), p.15.

Formalization Note: the tuple weights are a function `μ` on all tuples `Fin M → Fin (n+1)`, but
only the entries on `ℒ` (`InL P`) appear in the objective and the constraints, so `μ` is the
paper's `(λ_{i₁⋯i_M})_{(i₁,…,i_M)∈ℒ}`; `ϵ` and `‖ϵ‖` are as in `consistentSet`. The constraints do
not mention `S` (Remark 1, p.16). The objective coefficient `ρ_{i₁⋯i_M}(S) ∈ WithTop ℝ` is read as
a real number by `WithTop.untopD 0`; for `S ∋ 0` and tuples in `ℒ` it is finite, so the default
`0` is never used where the paper defines (2). The optimal value is `sInf` of the set of objective
values of feasible points: the objective is bounded below by `0` (as `r ≥ 0`), and the infimum is
attained when (2) is feasible (a linear objective over a compact polytope). -/
noncomputable def lpValue {n M : ℕ} (P : Problem n M) (S : Finset (Fin (n + 1))) : ℝ :=
  sInf {z : ℝ | ∃ (μ : (Fin M → Fin (n + 1)) → ℝ) (ε : Fin M → Fin (n + 1) → ℝ),
      (∀ t, InL P t → 0 ≤ μ t) ∧
      ∑ t ∈ Finset.univ.filter (InL P), μ t = 1 ∧
      errNorm P.norm P.S ε ≤ P.η ∧
      (∀ m, ∀ i ∈ P.S m,
        (∑ t ∈ Finset.univ.filter (fun t => InL P t ∧ t m = i), μ t) - ε m i = P.v m i) ∧
      z = ∑ t ∈ Finset.univ.filter (InL P), (rho P t S).untopD 0 * μ t}

end RankRobustAssort


