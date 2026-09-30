-- Prove2me | Definitions.Def_SingleMachineSched_AlphaJSched_AlphaPoints
-- name    : SingleMachineSched_AlphaJSched_AlphaPoints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:15:45.80499+00:00
-- url     : https://prove2.me/theorems/8cbf6f9d-906a-4ba3-89c2-c6bc6a52a8b1
-- title:
--   $\alpha$-points $t_j(\alpha)$, start times $t_j(0^+)$ and fractions $\eta_k(\alpha)$
-- statement:
--   Fix a preemptive schedule, given by the set $A_j\subseteq\mathbb R$ of times at which job $j$ is processed. For $0<\alpha\le1$, the **$\alpha$-point** of job $j$ is the first time at which $j$ has been processed for $\alpha p_j$ time units:
--   $$t_j(\alpha)=\inf\bigl\{t\in\mathbb R:\ \alpha p_j\le \lambda(A_j\cap(-\infty,t])\bigr\},$$
--   where $\lambda$ is Lebesgue measure. In particular $t_j(1)$ is the completion time of $j$. The **start time** $t_j(0^+)$ is $\inf A_j$. For a fixed job $j$ and $0<\alpha\le 1$, the fraction of job $k$ processed by time $t_j(\alpha)$ is
--   $$\eta_k(\alpha)=\frac{\lambda\bigl(A_k\cap(-\infty,t_j(\alpha)]\bigr)}{p_k};$$
--   in particular $\eta_j(\alpha)=\alpha$.
--
--   $\alpha$-points are how the preemptive LP schedule is converted into a nonpreemptive one: jobs are sequenced in the order of their $\alpha$-points.
--
--   **Formalization Note.** The definitions take the processing sets $A$ as an argument; the mission applies them to the LP schedule. The value of $t_j(\alpha)$ is meaningful only for $0<\alpha\le1$ (for $\alpha\le0$ the set is unbounded below), and every theorem of the mission restricts $\alpha$ to $(0,1]$ or has it there almost surely. The implicit dependence of $\eta_k$ on the fixed job $j$ is an explicit argument.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 176 (α-points, t_j(0+), η_k(α))

import Mathlib

namespace SingleMachineSched.AlphaJSched

open MeasureTheory

/-- The `α`-point `t_j(α)` of job `j` in the preemptive schedule with processing sets `A`
(p. 176): the first time at which `j` has been processed for `α p_j` time units. Meaningful for
`0 < α ≤ 1`. -/
noncomputable def alphaPoint {n : ℕ} (p : Fin n → ℕ) (A : Fin n → Set ℝ) (j : Fin n) (α : ℝ) :
    ℝ :=
  sInf {t : ℝ | α * (p j : ℝ) ≤ (volume (A j ∩ Set.Iic t)).toReal}

/-- The start time `t_j(0⁺)` of job `j` in the schedule with processing sets `A`: the infimum
of the times at which `j` is processed. -/
noncomputable def startTime {n : ℕ} (A : Fin n → Set ℝ) (j : Fin n) : ℝ :=
  sInf (A j)

/-- `η_k(α)` for a fixed job `j` (p. 176): the fraction of job `k` processed by time `t_j(α)`. -/
noncomputable def eta {n : ℕ} (p : Fin n → ℕ) (A : Fin n → Set ℝ) (j : Fin n) (α : ℝ)
    (k : Fin n) : ℝ :=
  (volume (A k ∩ Set.Iic (alphaPoint p A j α))).toReal / (p k : ℝ)

end SingleMachineSched.AlphaJSched


