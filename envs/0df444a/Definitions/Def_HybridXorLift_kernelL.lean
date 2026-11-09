-- Prove2me | Definitions.Def_HybridXorLift_kernelL
-- name    : HybridXorLift_kernelL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:03.642303+00:00
-- url     : https://prove2.me/theorems/603d9ec3-67fa-425b-ba4d-d353f2e40ed6
-- title:
--   One-bit kernel $L$ with $\tau = 1/(2q)$
-- statement:
--   For an integer $q \ge 1$ set $\tau = 1/(2q)$ and
--   $$
--   L = \begin{pmatrix} \cosh\tau & -\sinh\tau \\ -\sinh\tau & \cosh\tau \end{pmatrix},
--   $$
--   with rows and columns indexed by a bit value in $\{0,1\}$. $L$ shrinks the all-ones direction by $e^{-\tau}$ and stretches the sign direction by $e^{\tau}$; its tensor powers are the kernels of the potentials.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §3.2, Eq. (3.3), p.11 (PDF p.13)

import Mathlib

namespace HybridXorLift

/-- The one-bit kernel `L = [[cosh τ, −sinh τ], [−sinh τ, cosh τ]]` with `τ = 1/(2q)` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd),
§3.2, Eq. (3.3), p.11 (PDF p.13)). Rows and columns are indexed by a bit (`false` = 0,
`true` = 1). -/
noncomputable def kernelL (q : ℕ) : Matrix Bool Bool ℝ :=
  Matrix.of fun b b' =>
    if b = b' then Real.cosh (1 / (2 * (q : ℝ))) else -Real.sinh (1 / (2 * (q : ℝ)))

end HybridXorLift


