-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
-- name    : OAI_Analysis_CoulombTransport_BranchSeparation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:32:25.934856+00:00
-- url     : https://prove2.me/theorems/8c120d9b-90d7-4428-a0ad-50c6ea3aba49
-- title:
--   The five components of the splitting construction
-- statement:
--   For a set $K\subseteq\mathbb{R}^3$ and maps $H_0,\dots,H_3$ of $\mathbb{R}^3$, the five components are
--   $$
--   C_0=K,\qquad C_{i+1}=H_i(K)\quad(i=0,1,2,3) .
--   $$
--
--   The central compact set and its four transported copies carry the density. They are later shown to be pairwise separated.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/BranchSeparation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/BranchSeparation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CoulombCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.BranchSeparation

/-- The central compact set and its four transported copies. -/
def components (K : Set E3) (H : Fin 4 → E3 → E3) : Fin 5 → Set E3 :=
  Fin.cases K (fun i => H i '' K)

end Problem356.BranchSeparation

end

end OAI


