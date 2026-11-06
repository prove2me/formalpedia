-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsAdmissibleStage
-- name    : KawasakiSOS_Threshold_IsAdmissibleStage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:03:36.413406+00:00
-- url     : https://prove2.me/theorems/85d9c50f-4140-47db-bfc3-fc77ed9761b8
-- title:
--   Admissible stages
-- statement:
--   A stage $S$ is admissible for the pair $(x,y)$ if $r_z,r_w\ge0$, that is, if $z_{S,\xi},w_S\in\Omega$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_rz
import Definitions.Def_KawasakiSOS_Threshold_rw

namespace KawasakiSOS.Threshold

/-- The stage is admissible if `r_z, r_w ≥ 0`, i.e. if `z_{S,ξ}, w_S ∈ Ω`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12). -/
def IsAdmissibleStage {n k : ℕ} [NeZero k] (x y : Config n k) (S : Stage k) : Prop :=
  0 ≤ rz x y S ∧ 0 ≤ rw x y S

end KawasakiSOS.Threshold


