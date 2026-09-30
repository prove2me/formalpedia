-- Prove2me | Definitions.Def_SingleMachineSched_AlphaJSched_LPStructure
-- name    : SingleMachineSched_AlphaJSched_LPStructure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:16:24.531444+00:00
-- url     : https://prove2.me/theorems/d06bd018-389e-4568-acc0-5e8d11e05408
-- title:
--   The partition $N\setminus\{j\}=N_1\cup N_2$ and the fractions $\mu_k$ of the LP schedule
-- statement:
--   Fix a job $j$ and consider the LP schedule. Let $C^{LP}_j=\sup A^{LP}_j$ be the completion time of $j$ in it and $t_j(0^+)=\inf A^{LP}_j$ its start time. This file defines
--
--   1. $N_2$, the set of jobs $k\ne j$ that are processed between the start and the completion of job $j$, that is, for which $A^{LP}_k\cap(t_j(0^+),C^{LP}_j)$ has positive measure;
--   2. $N_1$, all remaining jobs $k\ne j$;
--   3. for a job $k$, the fraction of job $j$ that is processed before the start of job $k$,
--   $$\mu_k=\frac{\lambda\bigl(A^{LP}_j\cap(-\infty,t_k(0^+)]\bigr)}{p_j}.$$
--
--   In the LP schedule a job that is processed while $j$ is interrupted has smaller index and is completed before $j$ resumes. The partition into $N_1$ and $N_2$ captures this: $\eta_k(\alpha_j)$ does not depend on $\alpha_j$ for $k\in N_1$, and for $k\in N_2$ it is $0$ or $1$ according as $\alpha_j\le\mu_k$ or $\alpha_j>\mu_k$.
--
--   **Formalization Note.** The paper defines $\mu_k$ only for $k\in N_2$, where $0<\mu_k<1$; the definition here is total and is used only for $k\in N_2$. "Processed between the start and completion" is read as processing of positive duration strictly inside $(t_j(0^+),C^{LP}_j)$.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 182 (N_1, N_2, μ_k)

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_LPSchedule
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaPoints

namespace SingleMachineSched.AlphaJSched

open MeasureTheory

/-- The completion time of job `j` in the LP schedule: the supremum of its processing times. -/
noncomputable def lpCompletion {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) : ℝ :=
  sSup (lpSet p r j)

/-- `N₂` for the fixed job `j` (p. 182): the jobs `k ≠ j` processed (for a positive amount of
time) between the start and the completion of `j` in the LP schedule. -/
noncomputable def N2 {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun k => k ≠ j ∧
    0 < volume (lpSet p r k ∩ Set.Ioo (startTime (lpSet p r) j) (lpCompletion p r j)))

/-- `N₁` for the fixed job `j` (p. 182): all jobs other than `j` that are not in `N₂`. -/
noncomputable def N1 {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun k => k ≠ j ∧ k ∉ N2 p r j)

/-- `μ_k` for the fixed job `j` (p. 182): the fraction of job `j` processed in the LP schedule
before the start of job `k`. -/
noncomputable def mu {n : ℕ} (p r : Fin n → ℕ) (j k : Fin n) : ℝ :=
  (volume (lpSet p r j ∩ Set.Iic (startTime (lpSet p r) k))).toReal / (p j : ℝ)

end SingleMachineSched.AlphaJSched


