-- Prove2me | Definitions.Def_KarpLiptonOM_OracleTM_init
-- name    : KarpLiptonOM_OracleTM_init
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:22.64683+00:00
-- url     : https://prove2.me/theorems/1a289ae7-ff3f-4a21-8043-372bc6ecf6e8
-- title:
--   Initial configuration of an oracle machine
-- statement:
--   On input $w$ (a string over $\{0, 1, \#\}$), an oracle machine starts in its initial state with $w$ written on the work tape, the work head on the first symbol of $w$, and a blank query tape.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_Cfg

namespace KarpLiptonOM

/-- The initial configuration on input `w ∈ {0, 1, #}*`: initial state, `w` on the work tape with
the head on its first symbol, empty query tape (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20). -/
def OracleTM.init (M : OracleTM) (w : List (Option Bool)) : M.Cfg where
  state := M.q₀
  work := ⟨[], (w.map (fun s => some (M.ι s))).headD none, (w.map (fun s => some (M.ι s))).tail⟩
  query := ⟨[], none, []⟩

end KarpLiptonOM


