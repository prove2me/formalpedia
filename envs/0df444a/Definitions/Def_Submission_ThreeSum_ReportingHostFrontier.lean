-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
-- name    : Submission_ThreeSum_ReportingHostFrontier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:28:32.218012+00:00
-- url     : https://prove2.me/theorems/77dccf20-406c-4040-8738-c2f18a833a82
-- title:
--   Reporting Host Frontier
-- statement:
--   Definitions and structural lemmas for Reporting Host Frontier, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
set_option autoImplicit false
namespace ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
def children {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) : List (Finset (Fin (512*h))) :=
  if hk : k < J then localChildren ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) h else []
section Indices
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
def frontier {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) :=
  Reporting.frontier (children w.2.2) (prefixQuery I w) k
def candidates {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) :=
  (frontier I w k).flatMap fun pre => (children w.2.2 k).map fun S => pre ++ [S]
def generationWork {h J : ℕ} (I : Finset (RawItem h J α β γ)) (k : ℕ) : ℕ :=
  ∑ w : Wanted h J α,
    (frontier I w k).length*LightBlockChildren.time (J*(512*h)) (2*h) h
end Indices
end ThreeSum.ReportingHostFrontier


