-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_partitionFn
-- name    : KawasakiSOS_Threshold_partitionFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:57.509203+00:00
-- url     : https://prove2.me/theorems/1518556d-67c2-4615-bcce-619b5e58f33d
-- title:
--   The partition function $Z$
-- statement:
--   For real $\lambda>0$, the partition function of the model is
--
--   $$Z=\sum_{h\in\Omega_{n,k}}\lambda^{p(h)}.$$
--
--   It is the normalizing constant of the stationary measure $\pi$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_perimeter

namespace KawasakiSOS.Threshold

/-- The normalizing constant `Z = ∑_{h ∈ Ω} λ^{p(h)}` of the stationary measure.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2). -/
noncomputable def partitionFn (n k : ℕ) [NeZero k] (lam : ℝ) : ℝ :=
  ∑ h : Config n k, lam ^ perimeter h.1

end KawasakiSOS.Threshold


