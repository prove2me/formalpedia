-- Prove2me | Definitions.Def_StableMSR_SeparatorArenaLayout
-- name    : StableMSR_SeparatorArenaLayout
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-24T02:26:24.270801+00:00
-- url     : https://prove2.me/theorems/11b82241-f036-44ea-b5b5-07a7dae0308c
-- title:
--   The source prefix and eleven arrays used by the candidate enumerator
-- statement:
--   Take the first 45 instructions of the actual generator, up to the call to the geometry constructor. The named tables hold the active net, owners, piece, windows, adjacency, labels, representative rows, least elements, touching rows, masks and feasibility flags. Their specified base addresses are prefix sums of their lengths.
-- source:
--   Canonical integer implementation of the local construction in Appendix A.6, https://arxiv.org/abs/2611.03547

import Definitions.Def_StableMSR_LogicalCandidateProgram
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 35000
def listOf : Program → List Program
  | .seq p q=>p::listOf q | .skip=>[] | p=>[p]
def opening (h w:ℕ) := chain ((listOf (candidate h w)).take 7)
def arena := chain ((listOf src_generate).take 45)
def offsets (n M:ℕ) : List (ℕ×ℕ) :=
  [(71,n),(72,n),(73,n),(74,n*n),(75,n*n),(76,M),(77,n*M*n),
   (78,n*M*n),(79,n*M*n),(80,n*M*n*n),(81,n*M)]
def cursorAt (layout:List (ℕ×ℕ)) (j:ℕ) := ((layout.take j).map Prod.snd).sum
def sizes (n h:ℕ) := (h+1)*n^(2*(h+1))

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical


