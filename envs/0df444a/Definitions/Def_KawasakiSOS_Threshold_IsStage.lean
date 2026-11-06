-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsStage
-- name    : KawasakiSOS_Threshold_IsStage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:57.38012+00:00
-- url     : https://prove2.me/theorems/2be1902f-10d4-4afb-80ec-c9df053bb881
-- title:
--   Stages: disjoint windows
-- statement:
--   A stage is a pair $S=(c_A,c_B)$ of sites such that $W_A=W_A(c_A)$ and $W_B=\{c_B\}$ are disjoint.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_windowA

namespace KawasakiSOS.Threshold

/-- `S` is a stage: `W_A = W_A(c_A)` and `W_B = {c_B}` are disjoint.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12). -/
def IsStage {k : ℕ} (S : Stage k) : Prop := S.cB ∉ windowA S.cA

end KawasakiSOS.Threshold


