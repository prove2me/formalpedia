-- Prove2me | Definitions.Def_TPG_Markov
-- name    : TPG_Markov
-- status  : Definition
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:47:00.270796+00:00
-- url     : https://prove2.me/theorems/b65f800a-8c9f-4fcc-b661-f4c8d0eb642a
-- title:
--   Markov structure of the trajectory law: paths, head and tail, restarted environment, state distribution under time-varying randomization
-- statement:
--   Auxiliary objects for working with the trajectory law of `TPG_Model`. Time is $t=0,\dots,T-1$ (the source's $t+1$).
--
--   1. **Path embedding** (`embedPath x z y`): the trajectory $(x_t,z_t,y_t)_{t<T}$ with state path $x$, action path $z$ and rewards $y$.
--
--   2. **Head and tail** (`headTraj m n`, `tailTraj m n`): for a trajectory of length $m+n$, its first $m$ time steps, and its last $n$ time steps re-indexed from $0$.
--
--   3. **Reward law along a path** (`Env.rewardLaw x z`): the product measure $\bigotimes_{t<T}R(\cdot\mid x_t,z_t)$ on $\mathbb R^T$, i.e. the joint law of the rewards given the state and action paths.
--
--   4. **Restarted environment** (`Env.shift m a`): the environment whose kernel at its time $t$ is $P^{m+t}_z$, whose initial distribution is the point mass at the state $a$, and whose reward laws are unchanged. Its trajectory law is the law of the original process from time $m$ on, started at $X_m=a$.
--
--   5. **State distribution under time-varying randomization** (`Env.stateVec q t`): the row vector
--
--   $$\mu_q^t=\rho^\top P^0_{q_0}P^1_{q_1}\cdots P^{t-1}_{q_{t-1}},\qquad P^s_{\theta}=\theta P^s_1+(1-\theta)P^s_0 ,$$
--
--   which is the distribution of $X_t$ when the action at time $s$ is treatment with probability $q_s$.
--
--   These objects are used to state the mixture representation of the trajectory law, its Markov property, and the matrix formulas for expected rewards.
--
--   **Formalization Note** `Env.shift` and `Env.stateVec` need decidable equality on $S$ (for the point mass and the identity matrix).
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it formalizes §2.2, pp. 8–9 (Markov process, rewards), Appendix A.1, p. 27 (multi-step kernels), and the expectation E_{a_t,x} of the process started at X_{a_t}=x used in Appendix F.1, p. 40.

import Mathlib
import Definitions.Def_TPG_Model

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG

/-- The trajectory whose state path is `x`, whose action path is `z` and whose rewards are `y`. -/
def embedPath {S : Type} {T : ℕ} (x : Fin T → S) (z : Fin T → Bool) (y : Fin T → ℝ) :
    Traj S T :=
  fun t => (x t, z t, y t)

/-- The first `m` time steps of a trajectory of length `m + n`. -/
def headTraj {S : Type} (m n : ℕ) (ω : Traj S (m + n)) : Traj S m :=
  fun i => ω (Fin.castAdd n i)

/-- The last `n` time steps of a trajectory of length `m + n`, re-indexed from `0`. -/
def tailTraj {S : Type} (m n : ℕ) (ω : Traj S (m + n)) : Traj S n :=
  fun j => ω (Fin.natAdd m j)

section

variable {S : Type} [Fintype S]

/-- Joint law of the rewards along a fixed state path `x` and action path `z`:
independent coordinates with `Y_t ∼ R(· | x_t, z_t)`. -/
noncomputable def Env.rewardLaw (E : Env S) {T : ℕ} (x : Fin T → S) (z : Fin T → Bool) :
    Measure (Fin T → ℝ) :=
  Measure.pi (fun t => E.R (x t) (z t))

/-- The environment restarted at time `m` from the state `a`: the kernel used at its time `t`
is the original kernel of time `m + t`, the initial distribution is the point mass at `a`, and
the reward distributions are unchanged. -/
noncomputable def Env.shift [DecidableEq S] (E : Env S) (m : ℕ) (a : S) : Env S where
  P := fun t => E.P (m + t)
  P_nonneg := fun t => E.P_nonneg (m + t)
  P_row_sum := fun t => E.P_row_sum (m + t)
  ρ := fun x => if x = a then 1 else 0
  ρ_nonneg := fun x => by split_ifs <;> norm_num
  ρ_sum := by simp
  R := E.R
  R_prob := E.R_prob

/-- Row distribution of the state at time `t` when the action at time `s` is treatment with
probability `q s`: `ρᵀ P_{q_0}^0 P_{q_1}^1 ⋯ P_{q_{t-1}}^{t-1}`. -/
noncomputable def Env.stateVec [DecidableEq S] (E : Env S) (q : ℕ → ℝ) (t : ℕ) : S → ℝ :=
  Matrix.vecMul E.ρ ((List.range t).map (fun s => E.PMix (q s) s)).prod

end

end TPG


