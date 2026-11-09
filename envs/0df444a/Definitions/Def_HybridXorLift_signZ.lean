-- Prove2me | Definitions.Def_HybridXorLift_signZ
-- name    : HybridXorLift_signZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:04.982793+00:00
-- url     : https://prove2.me/theorems/bcd4ebda-c023-438d-9852-e303127b474b
-- title:
--   Sign matrix $Z = \mathrm{diag}(1,-1)$
-- statement:
--   The **sign matrix** of one physical bit is
--   $$
--   Z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix},
--   $$
--   indexed by a bit value: $Z_{bb} = (-1)^b$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §3.2, Eq. (3.3), p.11 (PDF p.13)

import Mathlib

namespace HybridXorLift

/-- The sign matrix `Z = diag(1, −1)` of one physical bit (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §3.2, Eq. (3.3), p.11 (PDF
p.13)), indexed by a bit (`false` = 0 ↦ `1`, `true` = 1 ↦ `−1`). -/
def signZ : Matrix Bool Bool ℝ :=
  Matrix.diagonal fun b => if b then -1 else 1

end HybridXorLift


