-- Prove2me | Definitions.Def_KarpLiptonOM_Tape_move
-- name    : KarpLiptonOM_Tape_move
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:26.283428+00:00
-- url     : https://prove2.me/theorems/a884fa9b-ecc9-40d0-ad71-a155dbd6377e
-- title:
--   Write a symbol and move the head
-- statement:
--   One elementary tape operation: the symbol $s$ is written on the scanned square and the head moves one square to the left or right. Moving right past the last written square scans a blank; moving left from the leftmost square scans a new blank square. This is exactly the tape update of one step of the published one-tape model `CookPvsNP`.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (machines); step of CookPvsNP_defs

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_Tape

namespace KarpLiptonOM

/-- Write `s` on the scanned square and move the head one square (the two cases of the published
Cook step `CookPvsNP.TM.step`; moving left from the leftmost square adds a blank square)
(Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20). -/
def Tape.move {Γ : Type} (t : Tape Γ) (s : Option Γ) : CookPvsNP.Move → Tape Γ
  | .right => ⟨s :: t.left, t.right.headD none, t.right.tail⟩
  | .left =>
    match t.left with
    | [] => ⟨[], none, s :: t.right⟩
    | a :: x => ⟨x, a, s :: t.right⟩

end KarpLiptonOM


