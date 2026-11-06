-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsComplement
-- name    : KawasakiSOS_Threshold_IsComplement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:05:33.174697+00:00
-- url     : https://prove2.me/theorems/0a445d62-20d6-4dc0-ad37-c887a93c8f85
-- title:
--   The complementary state $w$ of a segment
-- statement:
--   For a transition on the canonical path $\gamma_{xy}$, the complementary state $w$ depends on the segment of the path containing it: in the opening $w=y$, in the closing $w=x$, and in the realization of a slide $S\to S'$, $w=w_S$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Segment
import Definitions.Def_KawasakiSOS_Threshold_IsWState

namespace KawasakiSOS.Threshold

/-- The `w` of §4.7: in the opening `w = y`, in the closing `w = x`, in the realization of a slide `S → S′`, `w = w_S`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 14 (PDF p. 15). -/
def IsComplement {n k : ℕ} [NeZero k] (x y : Config n k) : Segment k → Config n k → Prop
  | .opening, w => w = y
  | .slide S _ _ _, w => IsWState x y S w
  | .closing, w => w = x

end KawasakiSOS.Threshold


