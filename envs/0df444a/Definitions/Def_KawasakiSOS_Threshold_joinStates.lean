-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_joinStates
-- name    : KawasakiSOS_Threshold_joinStates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:07.543066+00:00
-- url     : https://prove2.me/theorems/c09bce34-6e17-49cf-bda9-05b56f988aa0
-- title:
--   Concatenating the segments of a path
-- statement:
--   The canonical path is the concatenation of its segments. This definition gives the resulting list of states, with the state shared by two consecutive segments listed once.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Segment

namespace KawasakiSOS.Threshold

/-- The list of states of the concatenation of the segments: the shared state at each junction is listed once.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 14 (PDF p. 15). -/
def joinStates {n k : ℕ} [NeZero k] : List (Segment k × List (Config n k)) → List (Config n k)
  | [] => []
  | p :: rest => p.2 ++ (joinStates rest).tail

end KawasakiSOS.Threshold


