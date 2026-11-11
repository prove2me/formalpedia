-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_FiniteRun
-- name    : ConstrainedCorrelationRepulsion_Main_FiniteRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:31:38.331444+00:00
-- url     : https://prove2.me/theorems/d3ed1e5c-8c3e-407f-871f-968297f2378e
-- title:
--   Finite fixed-law execution and the direct zero-cost branch
-- statement:
--   The finite state records processed vertices and already output blocks. Each round samples from the original candidate law, repairs its intersection with unprocessed vertices, and appends those blocks. Completion appends every unprocessed unit separately. The LP is not recomputed and the candidate law is not conditioned on the remaining set.
--
--   The direct zero-cost branch uses connected components of the positive graph and tests their cost and hard feasibility. The nonzero branch uses the specified level and finite round count. This law is a mathematical execution specification; executable realizations and their charged complexity are theorem obligations, rather than fields of the state.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Figure 6 and §6.3, printed pp.13, 33–35 (PDF pp.14, 34–36)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Rounds
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Normalization

namespace ConstrainedCorrelationRepulsion.Main

open Classical

structure RoundState (n : ℕ) where
  processed : Finset (Fin n) := ∅
  output : List (Finset (Fin n)) := []

noncomputable def finiteRun {n : ℕ} (I : Instance n) (U : Units n)
    (y : LocalTable n) (r : ℕ) : ℕ → PMF (RoundState n)
  | 0 => PMF.pure {}
  | T+1 => (finiteRun I U y r T).bind fun st =>
      (candidateLaw I U y r).map fun C =>
        {processed := st.processed ∪ C,
         output := st.output ++ repair I (tableDistance U y) (C \ st.processed)}

/-- The finite executable sampling specification: one fixed LP table, fresh independent
candidates, intersection before repair, and one cluster per remaining unit at completion. -/
noncomputable def finiteRunLaw {n : ℕ} (I : Instance n) (U : Units n)
    (y : LocalTable n) (r T : ℕ) : PMF (Partition n) :=
  (finiteRun I U y r T).map fun st =>
    partitionOfBlocks (st.output ++ (U.blocks.filter (fun D => Disjoint D st.processed)).toList)

/-- The source's direct zero-cost check uses connected positive components, not an optimizer. -/
noncomputable def positiveComponentPartition {n : ℕ} (I : Instance n) : Partition n := fun v =>
  let C := Finset.univ.filter (fun u => I.positive.Reachable v u)
  C.min' (by exact ⟨v, by simp [C]⟩)

noncomputable def coreLaw {n : ℕ} (I J : Instance n) (U : Units n)
    (y : LocalTable n) (epsilon : ℚ) : PMF (Partition n) :=
  let P := positiveComponentPartition I
  if Feasible I P ∧ cost I P = 0 then PMF.pure P else
    finiteRunLaw J U y (level epsilon) (roundCount n (epsilon/4))

end ConstrainedCorrelationRepulsion.Main


