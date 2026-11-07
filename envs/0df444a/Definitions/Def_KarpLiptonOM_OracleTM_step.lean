-- Prove2me | Definitions.Def_KarpLiptonOM_OracleTM_step
-- name    : KarpLiptonOM_OracleTM_step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:58.288202+00:00
-- url     : https://prove2.me/theorems/c3da1368-d683-4157-8cbb-08990c244d8f
-- title:
--   One computation step of an oracle machine with oracle $O$
-- statement:
--   One **step** of an oracle machine with oracle language $O$ from a configuration $c$:
--
--   1. if $c$ is in the accepting or the rejecting state, nothing changes;
--   2. if $c$ is in the query state, the machine moves to $q_{\mathrm{yes}}$ when the string on the query tape is in $O$ and to $q_{\mathrm{no}}$ otherwise, and the tapes do not change;
--   3. otherwise the transition function, applied to the state and the two scanned symbols, gives the new state, the symbols to write and the head moves on both tapes.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.2, p.21 (oracle access)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_Cfg
import Definitions.Def_KarpLiptonOM_Tape_move
import Definitions.Def_KarpLiptonOM_Tape_bits

namespace KarpLiptonOM

/-- One step of an oracle machine with oracle language `O` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.2, p.21, Definition A.2.1):
halting configurations are fixed; in the query state the machine enters `qyes` if the query string
is in `O`, else `qno`; otherwise it applies `δ` to both tapes. -/
noncomputable def OracleTM.step (M : OracleTM) (O : Set (List Bool)) (c : M.Cfg) : M.Cfg := by
  classical exact
    if c.state = M.qaccept ∨ c.state = M.qreject then c
    else if c.state = M.qquery then
      { c with state := if c.query.bits M.ι ∈ O then M.qyes else M.qno }
    else
      let r := M.δ c.state c.work.head c.query.head
      { state := r.1, work := c.work.move r.2.1.1 r.2.1.2, query := c.query.move r.2.2.1 r.2.2.2 }

end KarpLiptonOM


