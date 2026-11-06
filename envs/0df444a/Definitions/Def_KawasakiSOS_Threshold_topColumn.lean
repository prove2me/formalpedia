-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_topColumn
-- name    : KawasakiSOS_Threshold_topColumn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:12.881194+00:00
-- url     : https://prove2.me/theorems/ad0a0177-95dc-4680-935d-4ddbac4210bb
-- title:
--   The smallest column at which $h$ is maximal
-- statement:
--   For $h\in\Omega$, this is the column $r$: the smallest column, in the order $0,1,\dots,k-1$, at which $h$ is maximal.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.10, p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config

namespace KawasakiSOS.Threshold

/-- `r`, the smallest column at which `h` is maximal, smallest in `ZMod.val`. Formalization Note: the set is nonempty since `ZMod k` is finite and nonempty, so the `sInf` junk value is not reached.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.10, p. 13 (PDF p. 14). -/
noncomputable def topColumn {n k : ℕ} [NeZero k] (h : Config n k) : ZMod k :=
  ((sInf {v : ℕ | v < k ∧ ∀ i, h.1 i ≤ h.1 (v : ZMod k)} : ℕ) : ZMod k)

end KawasakiSOS.Threshold


