-- Prove2me | Definitions.Def_DetDLP_W3C_FpBaseOne
-- name    : DetDLP_W3C_FpBaseOne
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T04:57:18.746655+00:00
-- url     : https://prove2.me/theorems/88f39900-605f-424e-931b-6e315a470810
-- title:
--   Finite-field base single-coordinate cycle
-- statement:
--   Construct one phase-4 decomposition and phase-5 row-update LoopRuns cycle from explicit oracle-answer and word-cap certificates.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpDecompOne

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpBaseOne

open FpStep FpTraceStep NineOracleLoop BlockLookup

/-- The phase-5 state after installing the row carried by decomposition answer `u`. -/
def updateState (s : FpState) (a u : List Bool) : FpState :=
  nextState (packState s) 4 (s.idx + 1) s.blocksWord a
    (rowPkt (s.p - 1) 0
      (initRowCounts (decodeBlocks s.blocksWord) (decodeFrames u) s.idx)) []

/-- Build one certified coordinate cycle. Oracle correctness and cap bounds
    remain explicit inputs; this lemma establishes the controller transitions. -/
def cycle_of_answers
    {R : List Bool → List Bool → Prop} {s : FpState}
    {a u final : List Bool} {cap : ℕ}
    (hphase : s.phase = 4)
    (hmore : s.idx < (decodeBlocks s.blocksWord).flatten.length + 2)
    (hdec : R (tag9 3 (queryInput 3
      (nextState (packState s) 5 s.idx s.blocksWord a [] []))) u)
    (hupdate : R (tag9 8 (queryInput 8 (updateState s a u))) final)
    (b0 : (pairWord (packState s) a).length ≤ cap)
    (b1 : (pairWord (packState (nextState (packState s) 5 s.idx s.blocksWord a [] []))
      (tag9 3 (queryInput 3 (nextState (packState s) 5 s.idx s.blocksWord a [] [])))).length ≤ cap)
    (b2 : u.length ≤ cap)
    (b3 : (pairWord (packState (nextState (packState s) 5 s.idx s.blocksWord a [] [])) u).length ≤ cap)
    (b4 : (pairWord (packState (updateState s a u))
      (tag9 8 (queryInput 8 (updateState s a u)))).length ≤ cap)
    (b5 : final.length ≤ cap) :
    FpDecompOne.Cycle R cap s (updateState s a u) a final := by
  let mid := nextState (packState s) 5 s.idx s.blocksWord a [] []
  have h4 : step resume (pairWord (packState s) a) =
      false :: pairWord (packState mid) (tag9 3 (queryInput 3 mid)) := by
    simpa [mid] using FpDecompPhase.phase4_decompose_step s a hphase hmore
  have h5 : step resume (pairWord (packState mid) u) =
      false :: pairWord (packState (updateState s a u))
        (tag9 8 (queryInput 8 (updateState s a u))) := by
    have hm : mid.phase = 5 := by simp [mid, nextState]
    rw [FpDecompPhase.phase5_update_step mid u hm]
    simp [updateState, mid, nextState]
  exact ⟨mid, tag9 3 (queryInput 3 mid), u,
    tag9 8 (queryInput 8 (updateState s a u)), h4, h5,
    b0, b1, b2, b3, b4, b5, hdec, hupdate⟩

end DetDLP.W3C.FpBaseOne


