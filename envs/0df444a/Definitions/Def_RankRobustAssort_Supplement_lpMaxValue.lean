-- Prove2me | Definitions.Def_RankRobustAssort_Supplement_lpMaxValue
-- name    : RankRobustAssort_Supplement_lpMaxValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:34:48.112821+00:00
-- url     : https://prove2.me/theorems/9a59c4ca-b733-4478-a2f0-00d4f21fa80a
-- title:
--   Optimal value of the linear program (EC.66)
-- statement:
--   For an assortment $S$, the optimal objective value of the linear optimization problem
--
--   $$
--   \begin{aligned}
--   \max_{\lambda,\epsilon}\ &\sum_{(i_1,\dots,i_M)\in\mathcal L}\xi_{i_1\cdots i_M}(S)\,\lambda_{i_1\cdots i_M}\\
--   \text{s.t. }&\sum_{(i_1,\dots,i_M)\in\mathcal L:\ i_m=i}\lambda_{i_1\cdots i_M}-\epsilon_{m,i}=v_{m,i}\quad\forall m\in\mathcal M,\ i\in S_m,\\
--   &\sum_{(i_1,\dots,i_M)\in\mathcal L}\lambda_{i_1\cdots i_M}=1,\qquad \|\epsilon\|\le\eta,\qquad \lambda_{i_1\cdots i_M}\ge0\ \ \forall(i_1,\dots,i_M)\in\mathcal L .
--   \end{aligned}
--   \tag{EC.66}
--   $$
--
--   Its constraints are those of the linear program (2); only the objective (with $\xi$ in place of $\rho$) and the sense change.
--
--   **Formalization Note.** The optimal value is the supremum of the objective over feasible points; it is attained when the program is feasible. The coefficient $\xi_{i_1\cdots i_M}(S)$ is read as a real number, which it is for $S\in\mathcal S$ and tuples in $\mathcal L$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Proposition EC.3, (EC.66), p.ec54

import Mathlib
import Definitions.Def_RankRobustAssort_errNorm
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_Supplement_xi

open Classical

namespace RankRobustAssort.Supplement

/-- The optimal objective value of the linear optimization problem (EC.66) for an assortment `S`:

maximize over `λ, ϵ`  `∑_{(i₁,…,i_M)∈ℒ} ξ_{i₁⋯i_M}(S) λ_{i₁⋯i_M}`
subject to `∑_{(i₁,…,i_M)∈ℒ : i_m = i} λ_{i₁⋯i_M} − ϵ_{m,i} = v_{m,i}` for all `m ∈ ℳ, i ∈ S_m`,
`∑_{(i₁,…,i_M)∈ℒ} λ_{i₁⋯i_M} = 1`, `‖ϵ‖ ≤ η`, `λ_{i₁⋯i_M} ≥ 0` for all `(i₁,…,i_M) ∈ ℒ`.

Sturt, arXiv:2112.05010v4, Proposition EC.3, (EC.66), p.ec54.

Formalization Note: the constraints are word for word those of the published `lpValue` (LP (2));
only the objective changes (`ξ` instead of `ρ`) and the sense (maximize). The tuple weights are a
function `μ` on all tuples, of which only the entries on `ℒ` (`InL P`) enter. The coefficient
`ξ_{i₁⋯i_M}(S) ∈ WithBot ℝ` is read as a real number by `WithBot.unbotD 0`; for `S ∋ 0` and tuples
in `ℒ` it is finite, so the default is never used where the paper defines (EC.66). The optimal
value is `sSup` of the set of objective values of feasible points: the objective is bounded above
by `r_n`, and the supremum is attained when (EC.66) is feasible (a linear objective over a compact
polytope). -/
noncomputable def lpMaxValue {n M : ℕ} (P : Problem n M) (S : Finset (Fin (n + 1))) : ℝ :=
  sSup {z : ℝ | ∃ (μ : (Fin M → Fin (n + 1)) → ℝ) (ε : Fin M → Fin (n + 1) → ℝ),
      (∀ t, InL P t → 0 ≤ μ t) ∧
      ∑ t ∈ Finset.univ.filter (InL P), μ t = 1 ∧
      errNorm P.norm P.S ε ≤ P.η ∧
      (∀ m, ∀ i ∈ P.S m,
        (∑ t ∈ Finset.univ.filter (fun t => InL P t ∧ t m = i), μ t) - ε m i = P.v m i) ∧
      z = ∑ t ∈ Finset.univ.filter (InL P), (xi P t S).unbotD 0 * μ t}

end RankRobustAssort.Supplement


