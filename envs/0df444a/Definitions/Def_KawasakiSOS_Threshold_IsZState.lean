-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsZState
-- name    : KawasakiSOS_Threshold_IsZState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:04:36.61217+00:00
-- url     : https://prove2.me/theorems/a630cd2c-63cb-4638-b784-54cd589fb528
-- title:
--   A configuration equal to $z_{S,\xi}$
-- statement:
--   The configuration $z\in\Omega$ is the vector $z_{S,\xi}$. Such a $z$ exists exactly when $r_z\ge0$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_zVec

namespace KawasakiSOS.Threshold

/-- The configuration `z` is `z_{S,ξ}`, i.e. their entries agree as integers.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12). -/
def IsZState {n k : ℕ} [NeZero k] (x y : Config n k) (S : Stage k) (ξ : ZMod k)
    (z : Config n k) : Prop :=
  ∀ i, (z.1 i : ℤ) = zVec x y S ξ i

end KawasakiSOS.Threshold


