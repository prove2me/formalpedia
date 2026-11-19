-- Prove2me | Definitions.Def_KoanaKPaths_Runtime_NatParser
-- name    : KoanaKPaths_Runtime_NatParser
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:50:48.642772+00:00
-- url     : https://prove2.me/theorems/0846df5d-844d-4a34-8d06-cf723f7596a0
-- title:
--   Self-delimiting natural-number parser
-- statement:
--   The input word code consists of a unary payload length, a zero separator, and the binary payload. The raw parser reads the length into markers, reads that many payload bits, restores their order through scratch storage, and adds the positive integer header. The bundle includes the transfer and counted-reading subprograms.
--
--   $$
--   \operatorname{wordCode}(W)=1^{|W|}\,0\,W.
--   $$
--
--   This parser is the shared bit-level foundation for the graph header and endpoint readers.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NatParser.lean; source snapshot SHA-256 32d4a7d75e6d80c6677b32667e0baf0b596da1ca06df35a5573c31039bb1cdc8.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S P : ℕ}

def transferBits (src dst : Fin S) : Stmt S P :=
  .loop src isBitT (.ite src (fun o => decide (o=some 0))
    (.seq (.pop src) (.push dst 0)) (.seq (.pop src) (.push dst 1)))

def unaryBody (tmp cnt : Fin S) : Stmt S P :=
  .seq (.pop tmp) (.seq (.push cnt 1) (.inRd tmp))

def readUnary (tmp cnt : Fin S) : Stmt S P :=
  .seq (.inRd tmp) (.seq (.loop tmp (fun o => decide (o=some 1)) (unaryBody tmp cnt)) (.pop tmp))

def readCountedBits (cnt dst : Fin S) : Stmt S P :=
  .loop cnt (fun o => decide (o=some 1)) (.seq (.pop cnt) (.inRd dst))

/-- Parse the self-delimiting binary natural-number code into an integer-item stack.
The three scratch stacks start empty and are restored. -/
def parseNat (tmp cnt rev dst : Fin S) : Stmt S P :=
  .seq (readUnary tmp cnt) (.seq (readCountedBits cnt rev)
    (.seq (transferBits rev dst) (.push dst hdPos)))





























def wordCode (W : List Bool) : List Sym := List.replicate W.length 1 ++ 0 :: W.map codeBit













end KoanaKPaths.Machine

end


