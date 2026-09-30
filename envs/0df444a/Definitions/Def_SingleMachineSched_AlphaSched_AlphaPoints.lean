-- Prove2me | Definitions.Def_SingleMachineSched_AlphaSched_AlphaPoints
-- name    : SingleMachineSched_AlphaSched_AlphaPoints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:09:50.387612+00:00
-- url     : https://prove2.me/theorems/771f0f04-358c-4d66-bb1a-a48132339e0a
-- title:
--   $\alpha$-points $t_j(\alpha)$, start times, the fractions $\eta_k(\alpha)$, and the structure $N_1, N_2, \mu_k$
-- statement:
--   Fix a preemptive schedule $(A_k)_k$ (in the theorems, the LP schedule).
--
--   1. For $0 < \alpha \le 1$, the **$\alpha$-point** of job $j$ is the first time at which $j$ has been processed for $\alpha p_j$ units:
--   $$t_j(\alpha) = \inf\{ t \in \mathbb R : |A_j \cap (-\infty, t]| \ge \alpha p_j \}.$$
--   In particular $t_j(1)$ is the completion time of $j$.
--   2. The **start time** of $j$ is $t_j(0^+) = \inf A_j$.
--   3. For a fixed job $j$ and $0 < \alpha \le 1$, $\eta_k(\alpha)$ is the fraction of job $k$ processed by time $t_j(\alpha)$:
--   $$\eta_k(\alpha) = \frac{|A_k \cap (-\infty, t_j(\alpha)]|}{p_k}.$$
--   In particular $\eta_j(\alpha) = \alpha$.
--
--   For the LP schedule and a fixed job $j$, with $C^{LP}_j = \sup A^{LP}_j$ the completion time of $j$ there:
--
--   4. $N_2$ is the set of jobs $k \ne j$ that the LP schedule processes (for a positive amount of time) between the start and the completion of job $j$;
--   5. $N_1$ is the set of all other jobs $k \ne j$;
--   6. for a job $k$, $\mu_k$ is the fraction of job $j$ processed before the start of job $k$:
--   $$\mu_k = \frac{|A^{LP}_j \cap (-\infty, t_k(0^+)]|}{p_j}.$$
--   The paper uses $\mu_k$ for $k \in N_2$, where $0 < \mu_k < 1$.
--
--   Here $|\cdot|$ is Lebesgue measure. These are the quantities in which the paper bounds completion times of the α-schedule.
--
--   **Formalization Note** $\eta_k$ depends on the fixed job $j$; the Lean definition takes $j$ as an explicit argument. The α-point is an infimum of reals; for $0 < \alpha \le 1$ and a bounded schedule the set is a nonempty closed half-line, so the infimum is its minimum. For $\alpha \le 0$ the set is all of $\mathbb R$ and Lean's infimum returns the junk value $0$, so every theorem restricts $\alpha$ to $(0, 1]$.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 176 ($\alpha$-points, $\eta_k$) and p. 182 ($N_1$, $N_2$, $\mu_k$)

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaSched_LPSchedule

namespace SingleMachineSched.AlphaSched

open MeasureTheory

/-- The `α`-point `t_j(α)` of job `j` in the preemptive schedule `A` (p. 176): the first time
at which `j` has been processed for `α p_j` time units. Meaningful for `0 < α ≤ 1`. -/
noncomputable def alphaPoint {n : ℕ} (p : Fin n → ℕ) (A : Fin n → Set ℝ) (j : Fin n) (α : ℝ) :
    ℝ :=
  sInf {t : ℝ | α * (p j : ℝ) ≤ (volume (A j ∩ Set.Iic t)).toReal}

/-- The start time `t_j(0⁺)` of job `j` in the schedule `A`: the infimum of its processing
times. -/
noncomputable def startTime {n : ℕ} (A : Fin n → Set ℝ) (j : Fin n) : ℝ :=
  sInf (A j)

/-- `η_k(α)` for a fixed job `j` (p. 176): the fraction of job `k` processed in the schedule
`A` by the time `t_j(α)`. -/
noncomputable def eta {n : ℕ} (p : Fin n → ℕ) (A : Fin n → Set ℝ) (j : Fin n) (α : ℝ)
    (k : Fin n) : ℝ :=
  (volume (A k ∩ Set.Iic (alphaPoint p A j α))).toReal / (p k : ℝ)

/-- The completion time of job `j` in the LP schedule: the supremum of its processing times. -/
noncomputable def lpCompletion {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) : ℝ :=
  sSup (lpSet p r j)

open Classical in
/-- `N₂` for a fixed job `j` (p. 182): the jobs other than `j` that the LP schedule processes
(for a positive amount of time) between the start and the completion of `j`. -/
noncomputable def N2 {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun k => k ≠ j ∧
    0 < volume (lpSet p r k ∩ Set.Ioo (startTime (lpSet p r) j) (lpCompletion p r j)))

open Classical in
/-- `N₁` for a fixed job `j` (p. 182): all jobs other than `j` that are not in `N₂`. -/
noncomputable def N1 {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun k => k ≠ j ∧ k ∉ N2 p r j)

/-- `μ_k` for a fixed job `j` (p. 182): the fraction of job `j` that the LP schedule processes
before the start of job `k`. -/
noncomputable def mu {n : ℕ} (p r : Fin n → ℕ) (j k : Fin n) : ℝ :=
  (volume (lpSet p r j ∩ Set.Iic (startTime (lpSet p r) k))).toReal / (p j : ℝ)

end SingleMachineSched.AlphaSched


