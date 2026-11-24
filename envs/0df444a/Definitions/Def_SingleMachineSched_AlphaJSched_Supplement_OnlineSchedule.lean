-- Prove2me | Definitions.Def_SingleMachineSched_AlphaJSched_Supplement_OnlineSchedule
-- name    : SingleMachineSched_AlphaJSched_Supplement_OnlineSchedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:08:51.291374+00:00
-- url     : https://prove2.me/theorems/ce983118-f583-41f0-8526-94e366f48424
-- title:
--   The on-line alpha-point schedule in real time
-- statement:
--   For a valid vector $0<\alpha_j\le1$, let $t_j(\alpha_j)$ be the published alpha-point in the LP schedule, and order jobs by these points, with index tie-break. Process jobs as early as possible in this order, subject to release and to not starting $k$ before $t_k(\alpha_k)$. Its completion times are
--   $$C^{\mathrm{on}}_j=\max_{k\preceq j}\left(\max\{r_k,t_k(\alpha_k)\}+\sum_{k\preceq i\preceq j}p_i\right).$$
--   This is the list-scheduling recurrence with effective release dates $\max\{r_k,t_k(\alpha_k)\}$. It supplies the delayed schedule of the competitive-ratio theorem.
--
--   **Formalization Note** Completions are real; alpha-points are never rounded to an integer. The maximum is finite and nonempty because $j\preceq j$. The construction uses the existing priority order and LP schedule, and asserts no performance bound by definition.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), DOI 10.1137/S089548019936223X, p. 188 (PDF 24), §3.5

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaJSchedule

namespace SingleMachineSched.AlphaJSched.Supplement

/-- Completion in the on-line-(α_j)-schedule (§3.5, p. 188): list scheduling
in α-point order with effective release `max r_k t_k(α_k)`, in real time. -/
noncomputable def onlineCompletion {n : ℕ} (p r : Fin n → ℕ) (α : Fin n → ℝ)
    (j : Fin n) : ℝ := by
  classical
  let K := Finset.univ.filter (fun k => precedes p r α k j)
  have hK : K.Nonempty := by
    refine ⟨j, ?_⟩
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨rfl, le_rfl⟩
  exact K.sup' hK (fun k =>
    max (r k : ℝ) (alphaPoint p (lpSet p r) k (α k)) +
      ∑ i ∈ Finset.univ.filter (fun i => precedes p r α k i ∧ precedes p r α i j),
        (p i : ℝ))

end SingleMachineSched.AlphaJSched.Supplement


