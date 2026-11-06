-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_peak
-- name    : KawasakiSOS_Threshold_peak
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:13.189542+00:00
-- url     : https://prove2.me/theorems/bd3c5e4f-2067-4e4c-a531-a9dfb54d035d
-- title:
--   The smallest maximizer $m$ of $F$
-- statement:
--   This is the smallest maximizer $m$ of $F$ on $[0,k]$. Since $F$ is piecewise linear, $m$ is an integer.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_partialSum

namespace KawasakiSOS.Threshold

/-- `m`, the smallest maximizer of `F`. Formalization Note: `F` is piecewise linear, so its smallest maximizer on `[0, k]` is an integer, and the search over integers suffices. The set is nonempty, so the `sInf` junk value is not reached.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11). -/
noncomputable def peak {n k : ℕ} [NeZero k] (x y : Config n k) (p0 : ZMod k) : ℕ :=
  sInf {j : ℕ | j ≤ k ∧ ∀ i, i ≤ k → partialSum x y p0 i ≤ partialSum x y p0 j}

end KawasakiSOS.Threshold


