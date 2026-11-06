-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_windows
-- name    : KawasakiSOS_Threshold_windows
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:01:01.032208+00:00
-- url     : https://prove2.me/theorems/63a0d49d-1db3-430c-ae59-324efdf04d8f
-- title:
--   The window set $W=W_A\cup W_B$
-- statement:
--   For a stage $S$, $W=W_A\cup W_B$ is the union of its two windows, five sites in all.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_windowA

namespace KawasakiSOS.Threshold

/-- `W = W_A ∪ W_B`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12). -/
def windows {k : ℕ} (S : Stage k) : Finset (ZMod k) := insert S.cB (windowA S.cA)

end KawasakiSOS.Threshold


