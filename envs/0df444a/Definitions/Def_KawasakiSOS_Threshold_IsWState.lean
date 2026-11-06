-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsWState
-- name    : KawasakiSOS_Threshold_IsWState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:04:06.720492+00:00
-- url     : https://prove2.me/theorems/628bf12c-e874-4f32-8b90-8145bc273d83
-- title:
--   A configuration equal to $w_S$
-- statement:
--   The configuration $w\in\Omega$ is the vector $w_S$. Such a $w$ exists exactly when $r_w\ge0$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_wVec

namespace KawasakiSOS.Threshold

/-- The configuration `w` is `w_S`, i.e. their entries agree as integers.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12). -/
def IsWState {n k : ℕ} [NeZero k] (x y : Config n k) (S : Stage k) (w : Config n k) : Prop :=
  ∀ i, (w.1 i : ℤ) = wVec x y S i

end KawasakiSOS.Threshold


