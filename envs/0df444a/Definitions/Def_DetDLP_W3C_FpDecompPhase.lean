-- Prove2me | Definitions.Def_DetDLP_W3C_FpDecompPhase
-- name    : DetDLP_W3C_FpDecompPhase
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T03:59:07.318377+00:00
-- url     : https://prove2.me/theorems/a43751d8-d7c7-5a7d-b221-a9af772efbeb
-- title:
--   Finite-field decomposition phase trace segment
-- statement:
--   Formalizes the phase 4 and phase 5 controller transitions for decomposition and initial row updates, together with a reusable two-round bounded LoopRuns composition lemma.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpTraceStep
import Definitions.Def_DetDLP_W3C_FpRowExec

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpDecompPhase

open FpStep FpTraceStep NineOracleLoop

/-- In phase 4, an unprocessed base coordinate is sent to decomposition slot 3;
    its answer is retained as the phase-5 scratch word. -/
theorem phase4_decompose_step (s : FpState) (a : List Bool)
    (hphase : s.phase = 4) (hmore : s.idx < (BlockLookup.decodeBlocks s.blocksWord).flatten.length + 2) :
    step resume (pairWord (packState s) a) =
      false :: pairWord (packState (nextState (packState s) 5 s.idx s.blocksWord a [] []))
        (tag9 3 (queryInput 3 (nextState (packState s) 5 s.idx s.blocksWord a [] []))) := by
  rw [round_eq s a (by omega)]
  have hsum : (BlockLookup.decodeBlocks s.blocksWord).flatten.length =
      ((BlockLookup.decodeBlocks s.blocksWord).map List.length).sum := by simp
  have hm : s.idx < ((BlockLookup.decodeBlocks s.blocksWord).map List.length).sum + 2 := by omega
  simp [resume, hphase, hm, hsum, emit, call, nextState]

/-- Once all base coordinates have been decomposed, phase 4 advances to the
    phase-6 probe setup. -/
theorem phase4_done_step (s : FpState) (a : List Bool)
    (hphase : s.phase = 4) (hdone : (BlockLookup.decodeBlocks s.blocksWord).flatten.length + 2 ≤ s.idx) :
    step resume (pairWord (packState s) a) =
      false :: pairWord (packState (nextState (packState s) 6 0 s.blocksWord a [] []))
        (tag9 6 (queryInput 6 (nextState (packState s) 6 0 s.blocksWord a [] []))) := by
  rw [round_eq s a (by omega)]
  have hsum : (BlockLookup.decodeBlocks s.blocksWord).flatten.length =
      ((BlockLookup.decodeBlocks s.blocksWord).map List.length).sum := by simp
  have hd : ((BlockLookup.decodeBlocks s.blocksWord).map List.length).sum + 2 ≤ s.idx := by omega
  simp [resume, hphase, hd, hsum, emit, call, nextState]

/-- Phase 5 installs the initial exact row using the decomposition answer in
    the scratch input; the controller then returns to phase 4 at the next index. -/
theorem phase5_update_step (s : FpState) (a : List Bool)
    (hphase : s.phase = 5) :
    step resume (pairWord (packState s) a) =
      false :: pairWord (packState (nextState (packState s) 4 (s.idx + 1) s.blocksWord s.repWord
        (rowPkt (s.p - 1) 0 (BlockLookup.initRowCounts (BlockLookup.decodeBlocks s.blocksWord)
          (BlockLookup.decodeFrames a) s.idx)) []))
        (tag9 8 (queryInput 8 (nextState (packState s) 4 (s.idx + 1) s.blocksWord s.repWord
          (rowPkt (s.p - 1) 0 (BlockLookup.initRowCounts (BlockLookup.decodeBlocks s.blocksWord)
            (BlockLookup.decodeFrames a) s.idx)) []))) := by
  rw [round_eq s a (by omega)]
  simp [resume, hphase, emit, call, nextState]

/-- The two-round LoopRuns constructor for one phase-4/phase-5 decomposition
    cycle.  The call certificates and word cap are supplied by the relevant
    base decomposition and HNF-update oracle specifications. -/
theorem decomposition_cycle
    {R : List Bool → List Bool → Prop} {s s' s'' : FpState}
    {answer query updateAnswer output nextAnswer finalOutput : List Bool} {cap rounds : ℕ}
    (h4 : step resume (pairWord (packState s) answer) = false :: pairWord (packState s') query)
    (h5 : step resume (pairWord (packState s') updateAnswer) = false :: pairWord (packState s'') output)
    (b0 : (pairWord (packState s) answer).length ≤ cap)
    (b1 : (pairWord (packState s') query).length ≤ cap)
    (b2 : updateAnswer.length ≤ cap)
    (b3 : (pairWord (packState s') updateAnswer).length ≤ cap)
    (b4 : (pairWord (packState s'') output).length ≤ cap)
    (b5 : nextAnswer.length ≤ cap)
    (hc0 : R query updateAnswer) (hc1 : R output nextAnswer)
    (tail : LoopRuns (step resume) R rounds (packState s'') nextAnswer finalOutput cap) :
    LoopRuns (step resume) R (rounds + 2) (packState s) answer finalOutput cap := by
  apply DetDLP.W3C.FpRowExec.call_round h4 b0 b1 b2 hc0
  apply DetDLP.W3C.FpRowExec.call_round h5 b3 b4 b5 hc1 tail

end DetDLP.W3C.FpDecompPhase


