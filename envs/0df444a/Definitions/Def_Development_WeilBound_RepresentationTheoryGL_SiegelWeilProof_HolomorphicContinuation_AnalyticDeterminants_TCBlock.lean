-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlock
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlock
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:41.541966+00:00
-- url     : https://prove2.me/theorems/dfb8a34d-84ab-5972-b3a6-bc5296e451aa
-- title:
--   TCBlock
-- statement:
--   Definitions and structural lemmas for TCBlock, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCBlock.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCHeights
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlockC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def vv (σ : Equiv.Perm (Fin n)) (r : Fin n) : Matrix (Fin n) (Fin n) ℂ := single r (σ r) 1
def epsE (j : ℕ) : Fin (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) ≃ Fin n :=
  finSumFinEquiv.symm.trans (((Fintype.equivFin (blkA (n := n) j)).symm.sumCongr
    (Fintype.equivFin (blkB (n := n) j)).symm).trans
      (((Equiv.refl _).sumCongr (eBq j)).trans (Equiv.sumCompl fun x => x ∈ blkA (n := n) j)))
end PositivityTheory.Rg.Sw.LVs.TC


