-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_arcU
-- name    : KawasakiSOS_Threshold_arcU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:51.703114+00:00
-- url     : https://prove2.me/theorems/e4b993b7-a935-4c3e-b71e-56060bc70f10
-- title:
--   The pending arc $U$
-- statement:
--   The two windows of a stage split $\mathbb Z_k$ into four arcs in cyclic order $T,W_A,U,W_B$. The pending arc $U$ consists of the sites strictly between $c_A+2$ and $c_B$ in clockwise order. It may be empty.
--
--   **Formalization Note** Clockwise order is the order of increasing index modulo $k$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Stage

namespace KawasakiSOS.Threshold

/-- The pending arc `U`: the sites strictly between `c_A + 2` and `c_B` clockwise. Formalization Note: clockwise is the direction of increasing index, and arcs are computed from `ZMod.val` of differences, so that they wrap correctly.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12). -/
def arcU {k : ℕ} [NeZero k] (S : Stage k) : Finset (ZMod k) :=
  Finset.univ.filter fun i =>
    0 < (i - (S.cA + 2)).val ∧ (i - (S.cA + 2)).val < (S.cB - (S.cA + 2)).val

end KawasakiSOS.Threshold


