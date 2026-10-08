-- Prove2me | Definitions.Def_TwoAgentSched_ParetoTotal_Pareto
-- name    : TwoAgentSched_ParetoTotal_Pareto
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:29:44.45198+00:00
-- url     : https://prove2.me/theorems/b5ba1677-4bc1-41b8-a49a-15ebead4cc42
-- title:
--   §3 and §11: nondominated schedules and nondominated pairs of 1‖ΣC^A_i ∘ f^B_max
-- statement:
--   Nondominated schedules and pairs for agent $A$'s total completion time $\sum C^A_i$ against agent $B$'s maximum cost $f^B_{\max}$ (Agnetis et al. 2004, §3 and §11), in the model of the definition `TwoAgentSched.ParetoTotal.Model`.
--
--   1. A schedule $\sigma$ of all jobs is **nondominated** if there is no schedule $\bar\sigma$ of all jobs with
--   $$\textstyle\sum C^A_h(\bar\sigma)\le\sum C^A_h(\sigma),\qquad f^B_{\max}(\bar\sigma)\le f^B_{\max}(\sigma),$$
--   and at least one of the two inequalities strict.
--   2. A **nondominated pair** is a pair $\bigl(\sum C^A_h(\sigma),\,f^B_{\max}(\sigma)\bigr)$ for a nondominated schedule $\sigma$. The set of nondominated pairs is what the scheme PP of §11 enumerates, with one schedule per pair.
--
--   Counting pairs rather than schedules matters: several nondominated schedules can share the same pair (for instance by swapping two identical jobs), and §11 associates one schedule with each pair.
--
--   **Formalization Note** The set of pairs is a `Set (ℝ × ℝ)`; $f^B_{\max}$ needs $0<n_B$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 231, §3 (nondominated schedules); p. 239, §11 (nondominated pairs, the set 𝒮)

import Mathlib
import Definitions.Def_TwoAgentSched_ParetoTotal_Model
import Definitions.Def_TwoAgentSched_TotalMax_Model

namespace TwoAgentSched.ParetoTotal

/-- The set of nondominated pairs of `1‖ΣC^A_i ∘ f^B_max` (§3, p. 231; §11, p. 239): the
objective pairs `(ΣC^A_i(σ), f^B_max(σ))` of the nondominated schedules `σ`. Several
nondominated schedules with the same pair contribute one element. -/
def ndPairs {nA nB : ℕ} (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ) :
    Set (ℝ × ℝ) :=
  {q | ∃ l : List (TwoAgentSched.MaxMax.Job nA nB), TwoAgentSched.TotalMax.IsNondominated hB p fB l ∧
    q = (TwoAgentSched.TotalMax.totalCompletionA p l, TwoAgentSched.MaxMax.maxCostB hB p fB l)}

end TwoAgentSched.ParetoTotal


