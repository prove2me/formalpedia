-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsMove
-- name    : KawasakiSOS_Threshold_IsMove
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:54.261202+00:00
-- url     : https://prove2.me/theorems/d523152e-5d4c-4f24-9644-fda3f214a93f
-- title:
--   A single move between adjacent columns
-- statement:
--   A configuration $z'$ arises from $z$ by a single move if $z'=z-e_i+e_j$ for adjacent columns $i,j$ with $z(i)\ge1$. These are the moves the Kawasaki chain proposes.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 6 (PDF p. 7)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_transfer
import Definitions.Def_KawasakiSOS_Threshold_stepSign

namespace KawasakiSOS.Threshold

/-- `z′` arises from `z` by moving one unit between adjacent columns: `z(i) ≥ 1` and `z′ = z − e_i + e_{i±1}`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 6 (PDF p. 7). -/
def IsMove {n k : ℕ} [NeZero k] (z z' : Config n k) : Prop :=
  ∃ (i : ZMod k) (s : Bool), 1 ≤ z.1 i ∧ z' = transfer z i (i + stepSign s)

end KawasakiSOS.Threshold


