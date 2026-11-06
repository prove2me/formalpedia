-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_teleportEndpoints
-- name    : KawasakiSOS_Threshold_teleportEndpoints
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:55.317685+00:00
-- url     : https://prove2.me/theorems/28b83f09-3752-40fa-b5d8-8d473727cdb0
-- title:
--   The endpoints of a sequence of teleports
-- statement:
--   For a sequence of teleports started at $z$, these are the configurations reached between teleports: $z$ itself and the configuration after each teleport. They exclude the intermediate states of the walks.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_transfer

namespace KawasakiSOS.Threshold

/-- The teleport endpoints: the configuration before the first teleport and after each teleport of the sequence.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 13 (PDF p. 14). -/
def teleportEndpoints {n k : ℕ} [NeZero k] : Config n k → List (ZMod k × ZMod k) → List (Config n k)
  | z, [] => [z]
  | z, (i, j) :: ops => z :: teleportEndpoints (transfer z i j) ops

end KawasakiSOS.Threshold


