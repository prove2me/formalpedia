-- Prove2me | Definitions.Def_SingleMachineSched_AlphaJSched_AlphaJSchedule
-- name    : SingleMachineSched_AlphaJSched_AlphaJSchedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:16:48.342485+00:00
-- url     : https://prove2.me/theorems/3ad78afe-d9df-4cd6-a5ad-a3ac0ed79445
-- title:
--   The $(\alpha_j)$-schedule and its completion times $C^{\boldsymbol\alpha}_j$
-- statement:
--   Let $\boldsymbol\alpha=(\alpha_1,\dots,\alpha_n)$ with $0<\alpha_j\le1$. The **$(\alpha_j)$-schedule** processes the jobs nonpreemptively, as early as possible, in nondecreasing order of their $\alpha_j$-points $t_j(\alpha_j)$ in the LP schedule; $C^{\boldsymbol\alpha}_j$ is the completion time of job $j$ in it.
--
--   Write $k\preceq j$ when $(t_k(\alpha_k),k)\le(t_j(\alpha_j),j)$ lexicographically. Scheduling the jobs as early as possible in the order $\preceq$ gives the completion times
--   $$C^{\boldsymbol\alpha}_j=\max_{k\preceq j}\Bigl(r_k+\sum_{i:\ k\preceq i\preceq j}p_i\Bigr),$$
--   since the machine starts some job $k\preceq j$ at its release date $r_k$ and then works without idling until $j$ completes. This file defines the order $\preceq$, the completion time of list scheduling in a given order by this formula, and $C^{\boldsymbol\alpha}_j$.
--
--   **Formalization Note.** The index tie-break is never used for $\boldsymbol\alpha\in(0,1]^n$: two different jobs cannot reach their $\alpha$-points at the same instant, since each is processed just before its $\alpha$-point. The closed form is equivalent to the recursion "start the next job at the maximum of its release date and the previous completion time". Completion times are natural numbers because $r$ and $p$ are.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 177 ((α_j)-schedule, C^α_j)

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_LPSchedule
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaPoints

namespace SingleMachineSched.AlphaJSched

/-- The order of the `(α_j)`-schedule (p. 177): `k` comes no later than `j` when
`(t_k(α_k), k) ≤ (t_j(α_j), j)` lexicographically, α-points taken in the LP schedule. -/
def precedes {n : ℕ} (p r : Fin n → ℕ) (α : Fin n → ℝ) (k j : Fin n) : Prop :=
  alphaPoint p (lpSet p r) k (α k) < alphaPoint p (lpSet p r) j (α j) ∨
    (alphaPoint p (lpSet p r) k (α k) = alphaPoint p (lpSet p r) j (α j) ∧ k ≤ j)

/-- Completion time of job `j` when the jobs are scheduled nonpreemptively, as early as
possible, in the order `prec` (a reflexive total order): the closed form
`C_j = max_{k ≼ j} (r_k + Σ_{k ≼ i ≼ j} p_i)` of list scheduling. -/
noncomputable def listCompletion {n : ℕ} (p r : Fin n → ℕ) (prec : Fin n → Fin n → Prop)
    (j : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun k => prec k j)).sup
    (fun k => r k + ∑ i ∈ Finset.univ.filter (fun i => prec k i ∧ prec i j), p i)

/-- `C^α_j`, the completion time of job `j` in the `(α_j)`-schedule for the vector `α`
(p. 177): the jobs are processed as early as possible, in nondecreasing order of their
`α_j`-points in the LP schedule. -/
noncomputable def alphaCompletion {n : ℕ} (p r : Fin n → ℕ) (α : Fin n → ℝ) (j : Fin n) : ℕ :=
  listCompletion p r (precedes p r α) j

end SingleMachineSched.AlphaJSched


