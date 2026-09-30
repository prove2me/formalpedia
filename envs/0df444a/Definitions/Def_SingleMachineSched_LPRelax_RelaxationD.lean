-- Prove2me | Definitions.Def_SingleMachineSched_LPRelax_RelaxationD
-- name    : SingleMachineSched_LPRelax_RelaxationD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:58:49.087287+00:00
-- url     : https://prove2.me/theorems/577d9eab-8f36-48a2-b335-ce1eb82e668d
-- title:
--   The preemptive time-indexed relaxation (D) with horizon $T$ and its optimal value $Z_D$
-- statement:
--   Let $T$ be a natural number, the **horizon**. The **preemptive time-indexed relaxation** (D) of Dyer and Wolsey has a real variable $y_{j\tau}$ for every job $j$ and every slot $\tau = r_j, \dots, T-1$, meant as "job $j$ is processed during $[\tau, \tau+1)$". It reads
--
--   $$Z_D = \min \sum_{j \in N} w_j C_j$$
--
--   subject to
--
--   1. $\sum_{j : r_j \le \tau} y_{j\tau} \le 1$ for $\tau = 0, 1, \dots, T-1$ (one job per slot);
--   2. $\sum_{\tau = r_j}^{T-1} y_{j\tau} = p_j$ for every job $j$;
--   3. $y_{j\tau} \ge 0$ for every job $j$ and $\tau = r_j, \dots, T-1$;
--
--   where $C_j$ is given by equation (2.1),
--
--   $$C_j = \frac12 p_j + \frac{1}{p_j} \sum_{\tau = r_j}^{T-1} \Big(\tau + \frac12\Big) y_{j\tau}.$$
--
--   The variables are real: (D) is a linear program, not an integer program.
--
--   The paper takes $T$ to be an upper bound on the makespan of an optimal schedule. The companion predicate used by the theorems says that $T$ bounds the makespan of *some* feasible nonpreemptive schedule: there are start times $s_j \ge r_j$ with $[s_j, s_j + p_j)$ pairwise disjoint and $s_j + p_j \le T$ for all $j$.
--
--   **Formalization Note** Variables are a function $y : N \times \mathbb N \to \mathbb R$; the variables that do not exist in the paper ($\tau < r_j$ or $\tau \ge T$) are required to be $0$, so the capacity constraint may sum over all jobs. Ranges $\tau = r_j, \dots, T-1$ are `Finset.Ico (r j) T`, which avoids natural-number subtraction. $Z_D$ is the infimum of the objective over the feasible set; when $T$ bounds some schedule's makespan the feasible set is nonempty and compact, so the infimum is attained and is the LP value.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 170, relaxation (D) and Eq. (2.1)

import Mathlib

namespace SingleMachineSched.LPRelax

/-- `T` bounds the makespan of some feasible nonpreemptive schedule: there are start times
`s_j ≥ r_j` such that no two jobs overlap and every job finishes by `T`. -/
def IsMakespanBound {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) : Prop :=
  ∃ s : Fin n → ℝ, (∀ j, (r j : ℝ) ≤ s j) ∧
    (∀ j k, j ≠ k → s j + p j ≤ s k ∨ s k + p k ≤ s j) ∧
    ∀ j, s j + p j ≤ T

/-- Feasibility for the preemptive time-indexed relaxation (D) with horizon `T` (p. 170).
The variable `y j τ` exists only for `r_j ≤ τ ≤ T - 1` and is `0` elsewhere. -/
def FeasibleD {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (y : Fin n → ℕ → ℝ) : Prop :=
  (∀ j τ, 0 ≤ y j τ) ∧
  (∀ j τ, (τ < r j ∨ T ≤ τ) → y j τ = 0) ∧
  (∀ τ < T, ∑ j, y j τ ≤ 1) ∧
  (∀ j, ∑ τ ∈ Finset.Ico (r j) T, y j τ = (p j : ℝ))

/-- Equation (2.1): `C_j = p_j/2 + (1/p_j) Σ_{τ=r_j}^{T-1} (τ + 1/2) y_{jτ}`. -/
noncomputable def completionD {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (y : Fin n → ℕ → ℝ)
    (j : Fin n) : ℝ :=
  (p j : ℝ) / 2 + (1 / (p j : ℝ)) * ∑ τ ∈ Finset.Ico (r j) T, ((τ : ℝ) + 1 / 2) * y j τ

/-- The objective of (D): `Σ_j w_j C_j` with `C_j` from (2.1). -/
noncomputable def objD {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ) (T : ℕ)
    (y : Fin n → ℕ → ℝ) : ℝ :=
  ∑ j, w j * completionD p r T y j

/-- `Z_D`, the optimal value of (D) with horizon `T`. When `IsMakespanBound p r T` holds the
feasible set is nonempty (the unit slots of a left-shifted nonpreemptive schedule), and it is
compact (`0 ≤ y ≤ 1` on finitely many coordinates, zero elsewhere), so this infimum is the LP
value; if (D) is infeasible the infimum is the junk value `sInf ∅ = 0`. -/
noncomputable def zD {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ) (T : ℕ) : ℝ :=
  sInf ((fun y => objD p r w T y) '' {y | FeasibleD p r T y})

end SingleMachineSched.LPRelax


