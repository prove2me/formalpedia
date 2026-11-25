-- Prove2me | Definitions.Def_DetDLP_W3C_FpBaseChain
-- name    : DetDLP_W3C_FpBaseChain
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T05:18:39.570381+00:00
-- url     : https://prove2.me/theorems/4881cf4d-1ac8-5aa3-873b-1f9e6de6189a

import Definitions.Def_DetDLP_W3C_FpBaseOne
import Definitions.Def_DetDLP_W3C_FpDecompLoop

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpBaseChain

open FpStep FpTraceStep NineOracleLoop BlockLookup

/-- The final phase-4 controller transition enters phase 6 at root index zero. -/
theorem enterRoot (s : FpState) (a : List Bool)
    (hphase : s.phase = 4)
    (hdone : (decodeBlocks s.blocksWord).flatten.length + 2 ≤ s.idx) :
    step resume (pairWord (packState s) a) =
      false :: pairWord
        (packState (nextState (packState s) 6 0 s.blocksWord a [] []))
        (tag9 6 (queryInput 6
          (nextState (packState s) 6 0 s.blocksWord a [] []))) := by
  exact FpDecompPhase.phase4_done_step s a hphase hdone

/-- A chain transports an invariant when each certified single-coordinate
    cycle has the supplied invariant-preservation property. -/
theorem chainInvariant {R : List Bool → List Bool → Prop} {cap n : ℕ}
    {s endState : FpState} {a endAnswer : List Bool}
    [NeZero (s.p - 1)]
    (z : w3_Label (s.p - 1) ((decodeBlocks s.blocksWord).flatten.length + 2))
    (repOf : FpState → w3_Rep (s.p - 1) ((decodeBlocks s.blocksWord).flatten.length + 2))
    (chain : FpDecompLoop.Chain R cap n s a endState endAnswer)
    (preserves : ∀ {x y : FpState} {u v : List Bool},
      FpDecompOne.Cycle R cap x y u v →
      Stage2Trace.Invariant z (repOf x) → Stage2Trace.Invariant z (repOf y))
    (initial : Stage2Trace.Invariant z (repOf s)) :
    Stage2Trace.Invariant z (repOf endState) :=
  FpDecompLoop.chain_preserves (fun x => Stage2Trace.Invariant z (repOf x))
    chain preserves initial

/-- Combine a complete coordinate chain with the terminal phase-4 transition.
    The supplied endpoint facts state that the chain covers all factor-base
    coordinates and that its final answer is the current output word. -/
theorem chain_to_root {R : List Bool → List Bool → Prop} {cap n : ℕ}
    {s endState : FpState} {a endAnswer : List Bool}
    (chain : FpDecompLoop.Chain R cap n s a endState endAnswer)
    (hphase : endState.phase = 4)
    (hdone : (decodeBlocks endState.blocksWord).flatten.length + 2 ≤ endState.idx)
    (hidx : endState.idx = (decodeBlocks endState.blocksWord).flatten.length + 2)
    (hblocks : endState.blocksWord = s.blocksWord) :
    ∃ rootState rootAnswer,
      rootState.phase = 6 ∧ rootState.idx = 0 ∧
      step resume (pairWord (packState endState) endAnswer) =
        false :: pairWord (packState rootState) rootAnswer := by
  let rootState := nextState (packState endState) 6 0 endState.blocksWord endAnswer [] []
  let rootAnswer := tag9 6 (queryInput 6 rootState)
  refine ⟨rootState, rootAnswer, ?_, ?_, ?_⟩
  · simp [rootState, nextState]
  · simp [rootState, nextState]
  · simpa [rootState, rootAnswer] using enterRoot endState endAnswer hphase hdone

end DetDLP.W3C.FpBaseChain


