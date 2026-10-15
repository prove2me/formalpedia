-- Prove2me | Definitions.Def_OnlineMaxWeightMatch_Approx_LPMatch
-- name    : OnlineMaxWeightMatch_Approx_LPMatch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:42.511266+00:00
-- url     : https://prove2.me/theorems/d025faaf-6268-4ca1-8501-bf8172b2285f
-- title:
--   The linear program LP-Match, its optimal value and optimal solutions
-- statement:
--   Let $I$ be a RideHail instance with bins $i$, balls $t$ (in arrival order), arrival probabilities $p_t$ and weights $w_{i,t}$. **LP-Match** is the linear program in variables $x=(x_{i,t})$, read as "the probability that the online algorithm matches ball $t$ to bin $i$":
--
--   $$
--   \begin{aligned}
--   \max\ & \textstyle\sum_{i,t} w_{i,t}\,x_{i,t}\\
--   \text{s.t. } & \textstyle\sum_t x_{i,t}\le 1 && \text{for all } i, \quad(9)\\
--   & \textstyle\sum_i x_{i,t}\le p_t && \text{for all } t, \quad(10)\\
--   & \textstyle x_{i,t}\le p_t\big(1-\sum_{t'<t}x_{i,t'}\big) && \text{for all } i,t, \quad(11)\\
--   & x_{i,t}\ge 0 && \text{for all } i,t. \quad(12)
--   \end{aligned}
--   $$
--
--   $\mathrm{LP\text{-}Match}(I)$ denotes its optimal value, and an **optimal solution** is a feasible $x$ attaining it. Constraint (11), with the sum over balls $t'$ strictly before $t$, is what distinguishes LP-Match from the usual offline relaxation: it is valid for online algorithms, because the arrival of $t$ is independent of what the algorithm did before $t$, and not for offline ones.
--
--   **Formalization Note** $\mathrm{LP\text{-}Match}(I)$ is the supremum of the objective over the feasible set; that set is nonempty ($x=0$) and bounded ($0\le x_{i,t}\le 1$), so the supremum is a real maximum (attainment is checked in a local sorry-free verification file).
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 10, LP-Match, constraints (9)–(12)

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_RideHail

namespace OnlineMaxWeightMatch.Approx

variable {ι : Type*} {n : ℕ}

/-- `Σ_{t' < t} x_{i,t'}`: the LP mass of bin `i` on the balls strictly before ball `t`. -/
noncomputable def cumX (x : ι → Fin n → ℝ) (i : ι) (t : Fin n) : ℝ :=
  ∑ s ∈ Finset.Iio t, x i s

/-- Feasibility for the linear program **LP-Match** (p. 10), constraints (9)–(12). -/
structure LPFeasible [Fintype ι] (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) : Prop where
  /-- (9): `Σ_t x_{i,t} ≤ 1` for every bin `i` -/
  bin_le_one : ∀ i, ∑ t, x i t ≤ 1
  /-- (10): `Σ_i x_{i,t} ≤ p_t` for every ball `t` -/
  ball_le_p : ∀ t, ∑ i, x i t ≤ I.p t
  /-- (11): `x_{i,t} ≤ p_t · (1 - Σ_{t' < t} x_{i,t'})` for every edge -/
  online : ∀ i t, x i t ≤ I.p t * (1 - cumX x i t)
  /-- (12): `x_{i,t} ≥ 0` for every edge -/
  nonneg : ∀ i t, 0 ≤ x i t

/-- The objective of LP-Match, `Σ_{i,t} w_{i,t} · x_{i,t}`. -/
noncomputable def lpObjective [Fintype ι] (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ t, I.w i t * x i t

/-- `LP-Match(I)`: the optimal value of LP-Match, the supremum of the objective over the
feasible set (nonempty, since `x = 0` is feasible, and bounded, since `0 ≤ x ≤ 1`). -/
noncomputable def lpValue [Fintype ι] (I : RideHailInstance ι n) : ℝ :=
  sSup (lpObjective I '' {x | LPFeasible I x})

/-- `x` is an optimal solution of LP-Match. -/
def IsLPOptimal [Fintype ι] (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) : Prop :=
  LPFeasible I x ∧ lpObjective I x = lpValue I

end OnlineMaxWeightMatch.Approx


