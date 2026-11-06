-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_reservoirSites
-- name    : KawasakiSOS_Threshold_reservoirSites
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:00.750197+00:00
-- url     : https://prove2.me/theorems/23c77650-6c03-4ea3-88d9-8915788d0ac6
-- title:
--   The reservoir sites $R(S)$
-- statement:
--   A site of $W$ whose two neighbors both lie in $W$ is a reservoir site of the stage $S$, and $R(S)$ is the set of reservoir sites. It contains the interior of $W_A$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_windows

namespace KawasakiSOS.Threshold

/-- `R(S)`: the sites of `W` whose two neighbours both lie in `W`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12). -/
def reservoirSites {k : ℕ} (S : Stage k) : Finset (ZMod k) :=
  (windows S).filter fun i => i - 1 ∈ windows S ∧ i + 1 ∈ windows S

end KawasakiSOS.Threshold


