-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_wVec
-- name    : KawasakiSOS_Threshold_wVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:03:10.228201+00:00
-- url     : https://prove2.me/theorems/d048c56e-5cac-4ab0-9f86-2f0a5a81b8f9
-- title:
--   The complementary vector $w_S$
-- statement:
--   For a stage $S$, the vector $w_S$ equals $x$ on $T$, equals $y$ on $U$, and is $0$ on $W$, except for a reservoir of mass $r_w$ at $c_A$. It stores what the intermediate state $z_{S,\xi}$ has forgotten.
--
--   **Formalization Note** The vector has integer entries, so it is defined before admissibility is known.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_arcT
import Definitions.Def_KawasakiSOS_Threshold_arcU
import Definitions.Def_KawasakiSOS_Threshold_rw

namespace KawasakiSOS.Threshold

/-- The vector `w_S`: `x` on `T`, `y` on `U`, and `0` on `W` except for a reservoir of mass `r_w` at `c_A`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12). -/
def wVec {n k : ℕ} [NeZero k] (x y : Config n k) (S : Stage k) : ZMod k → ℤ :=
  fun i => if i ∈ arcT S then (x.1 i : ℤ) else if i ∈ arcU S then (y.1 i : ℤ)
    else if i = S.cA then rw x y S else 0

end KawasakiSOS.Threshold


