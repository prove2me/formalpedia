-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlockC
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlockC
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:25.541629+00:00
-- url     : https://prove2.me/theorems/2176a838-d51d-5ca6-8004-789672e8cd04
-- title:
--   TCBlock C
-- statement:
--   Definitions and structural lemmas for TCBlock C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCBlockC.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlockA
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_mem_blkB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
def eBq (j : ℕ) : {x // x ∈ blkB (n := n) j} ≃ {x // ¬ x ∈ blkA (n := n) j} :=
  Equiv.subtypeEquivRight (fun x => mem_blkB j x)
def piP (j : ℕ) (σA : Equiv.Perm (blkA (n := n) j)) (τ : Equiv.Perm (blkB (n := n) j)) : Equiv.Perm (Fin n) :=
  Equiv.Perm.subtypeCongr σA ((eBq j).permCongr τ)
def resA (j : ℕ) (σ : Equiv.Perm (Fin n)) (h : ∀ r, r ∈ blkA (n := n) j ↔ σ r ∈ blkA (n := n) j) :
    Equiv.Perm (blkA (n := n) j) :=
  σ.subtypePerm fun r => (h r).symm
def resB (j : ℕ) (σ : Equiv.Perm (Fin n)) (h : ∀ r, r ∈ blkA (n := n) j ↔ σ r ∈ blkA (n := n) j) :
    Equiv.Perm (blkB (n := n) j) :=
  (eBq j).symm.permCongr (σ.subtypePerm (p := fun x => ¬ x ∈ blkA (n := n) j) fun r => not_congr (h r).symm)
end PositivityTheory.Rg.Sw.LVs.TC


