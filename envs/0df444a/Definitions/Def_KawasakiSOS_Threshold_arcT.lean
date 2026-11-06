-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_arcT
-- name    : KawasakiSOS_Threshold_arcT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:37.961898+00:00
-- url     : https://prove2.me/theorems/c6f650c2-d3ec-4760-a7f7-466094439d1f
-- title:
--   The finished arc $T$
-- statement:
--   The finished arc $T$ of a stage consists of the sites strictly between $c_B$ and $c_A-1$ in clockwise order. It may be empty.
--
--   **Formalization Note** Clockwise order is the order of increasing index modulo $k$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Stage

namespace KawasakiSOS.Threshold

/-- The finished arc `T`: the sites strictly between `c_B` and `c_A − 1` clockwise.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12). -/
def arcT {k : ℕ} [NeZero k] (S : Stage k) : Finset (ZMod k) :=
  Finset.univ.filter fun i =>
    0 < (i - S.cB).val ∧ (i - S.cB).val < (S.cA - 1 - S.cB).val

end KawasakiSOS.Threshold


