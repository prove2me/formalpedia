-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_Segment
-- name    : KawasakiSOS_Threshold_Segment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:01:06.805199+00:00
-- url     : https://prove2.me/theorems/ce3f7e07-894b-4043-beae-ec71ef0e99d7
-- title:
--   Segments of a canonical path
-- statement:
--   A canonical path consists of segments of three kinds: the opening, the realization of a slide $S\to S'$ with reservoir sites $\xi,\xi'$, and the closing.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Stage

namespace KawasakiSOS.Threshold

/-- The kinds of segment of the canonical path: the opening, the realization of a slide `S → S′` with reservoirs `ξ`, `ξ′`, and the closing.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 14 (PDF p. 15). -/
inductive Segment (k : ℕ) where
  | opening : Segment k
  | slide (S S' : Stage k) (ξ ξ' : ZMod k) : Segment k
  | closing : Segment k

end KawasakiSOS.Threshold


