-- Prove2me | Definitions.Def_IgnallSchrage_Makespan_RefinedLowerBound
-- name    : IgnallSchrage_Makespan_RefinedLowerBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:30:42.550346+00:00
-- url     : https://prove2.me/theorems/11d09559-c0e7-45cd-820d-de036b345cac
-- title:
--   The refined three-machine lower bound used in the computations (p. 409)
-- statement:
--   For a node $J_r$ with unscheduled set $\bar J_r\neq\emptyset$, the refined bound is the bound $LB(J_r)$ of p. 401 in which $\mathrm{TIMEB}(J_r)$ is replaced by
--
--   $$
--   \max\big[\mathrm{TIMEB}(J_r),\ \mathrm{TIMEA}(J_r)+\min_{i\in\bar J_r}a_i\big]
--   $$
--
--   and $\mathrm{TIMEC}(J_r)$ is replaced by
--
--   $$
--   \max\big[\mathrm{TIMEC}(J_r),\ \mathrm{TIMEB}(J_r)+\min_{i\in\bar J_r}b_i,\ \mathrm{TIMEA}(J_r)+\min_{i\in\bar J_r}(a_i+b_i)\big].
--   $$
--
--   The replacements are earliest times at which machines $B$ and $C$ can start the next unscheduled job, so the refined bound is never smaller than $LB(J_r)$. The paper reports that this bound was the one used in its three-machine computations.
--
--   **Formalization Note** The $\mathrm{TIMEA}$ and $\mathrm{TIMEB}$ appearing inside the replacements are the original ones. As for $LB$, the minima use the placeholder $0$ on an empty $\bar J_r$, a value no statement evaluates. The bars over $\bar J_r$ are not visible in the scan.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 409, refined lower bound ("A lower bound slightly more sophisticated than the one given previously was used")

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound

namespace IgnallSchrage.Makespan

/-- The refined lower bound of p. 409: the bound `lowerBound` of p. 401 with
`TIMEB(J_r)` replaced by `max [TIMEB(J_r), TIMEA(J_r) + min_{J̄_r} a_i]` and
`TIMEC(J_r)` replaced by
`max [TIMEC(J_r), TIMEB(J_r) + min_{J̄_r} b_i, TIMEA(J_r) + min_{J̄_r} (a_i + b_i)]`
(the original, unreplaced `TIMEA`, `TIMEB` inside the replacements). Meant for nodes with
`J̄_r` nonempty. -/
def refinedLowerBound {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  let t := times a b c J
  let U := unscheduled J
  let tB := max t.2.1 (t.1 + minOver U a)
  let tC := max t.2.2 (max (t.2.1 + minOver U b) (t.1 + minOver U (fun i => a i + b i)))
  max (t.1 + ∑ i ∈ U, a i + minOver U (fun i => b i + c i))
    (max (tB + ∑ i ∈ U, b i + minOver U c)
      (tC + ∑ i ∈ U, c i))

end IgnallSchrage.Makespan


