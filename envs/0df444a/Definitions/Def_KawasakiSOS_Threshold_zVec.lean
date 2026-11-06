-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_zVec
-- name    : KawasakiSOS_Threshold_zVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:03:33.046057+00:00
-- url     : https://prove2.me/theorems/30f41909-c479-4a18-bc3c-9de1cf332e23
-- title:
--   The stage vector $z_{S,\xi}$
-- statement:
--   For a stage $S$ and $\xi\in R(S)$, the vector $z_{S,\xi}$ equals $y$ on $T$, equals $x$ on $U$, and is $0$ on $W$, except for a reservoir of mass $r_z$ at $\xi$. So the part of the cycle already processed shows the target $y$, and the part still pending shows the source $x$.
--
--   **Formalization Note** The vector has integer entries, so it is defined before admissibility is known.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_arcT
import Definitions.Def_KawasakiSOS_Threshold_arcU
import Definitions.Def_KawasakiSOS_Threshold_rz

namespace KawasakiSOS.Threshold

/-- The vector `z_{S,ξ}`: `y` on `T`, `x` on `U`, and `0` on `W` except for a reservoir of mass `r_z` at `ξ`. Formalization Note: integer valued; it is a configuration exactly when the stage is admissible.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12). -/
def zVec {n k : ℕ} [NeZero k] (x y : Config n k) (S : Stage k) (ξ : ZMod k) : ZMod k → ℤ :=
  fun i => if i ∈ arcT S then (y.1 i : ℤ) else if i ∈ arcU S then (x.1 i : ℤ)
    else if i = ξ then rz x y S else 0

end KawasakiSOS.Threshold


