-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_cycleBase
-- name    : KawasakiSOS_Threshold_cycleBase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:03:00.343224+00:00
-- url     : https://prove2.me/theorems/34c663dc-3152-44ab-893c-9911b193cb3b
-- title:
--   The smallest base column $p_0$
-- statement:
--   By the cycle lemma there is a column $p_0$ such that every partial sum of $d$ started at $p_0$ is nonnegative. This definition takes the smallest such column, with columns ordered as $0,1,\dots,k-1$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_IsCycleBase

namespace KawasakiSOS.Threshold

/-- The smallest column `p0` satisfying `IsCycleBase`, smallest in `ZMod.val`. Formalization Note: the set is nonempty by the cycle lemma [DM47], which the paper cites; the `sInf` junk value `0` is therefore never reached.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11). -/
noncomputable def cycleBase {n k : ℕ} [NeZero k] (x y : Config n k) : ZMod k :=
  ((sInf {v : ℕ | v < k ∧ IsCycleBase x y (v : ZMod k)} : ℕ) : ZMod k)

end KawasakiSOS.Threshold


