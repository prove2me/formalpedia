-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_LPSize
-- name    : ConstrainedCorrelationRepulsion_Main_LPSize
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:31:38.517692+00:00
-- url     : https://prove2.me/theorems/d559aac8-9ae3-4336-acd2-4d3f86ff8b16
-- title:
--   Variable and constraint counts for the bounded LP
-- statement:
--   The LP size counts its size-layered variables, coverage equations, disjoint inclusion–exclusion inequalities, vertex-weighted size equations, and hard-pair equations. Only indices of the specified order are included.
--
--   This count is computed from the finite input and is bounded in Lemma 5.1 by $n^{O(r)}$, together with an operational rational LP solver and a polynomial bit-length bound. No LP solver is an instruction or an input field.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Definition 2.5 and Lemma 5.1 proof, printed pp.9, 22–23 (PDF pp.10, 23–24)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Encoding

namespace ConstrainedCorrelationRepulsion.Main

open Classical
open scoped BigOperators

noncomputable def localIndices {n : ℕ} (U : Units n) (r : ℕ) :
    Finset (Finset (Finset (Fin n))) := U.blocks.powerset.filter (fun T => T.card ≤ r)

/-- The actual numbers of variables and equations/inequalities in (2)–(5), including
nonnegativity through inclusion–exclusion. This is a size count, not an input promise. -/
noncomputable def lpSize {n : ℕ} (I : Instance n) (U : Units n) (r : ℕ) : ℕ :=
  n * (localIndices U r).card + U.blocks.card +
  n * ((U.blocks.powerset ×ˢ U.blocks.powerset).filter (fun ST =>
    Disjoint ST.1 ST.2 ∧ ST.1.card + ST.2.card ≤ r)).card +
  n * (U.blocks.powerset.filter (fun T => T.card + 1 ≤ r)).card +
  n * ((U.blocks ×ˢ U.blocks).filter (fun BD => HardProduct I BD.1 BD.2)).card

end ConstrainedCorrelationRepulsion.Main


