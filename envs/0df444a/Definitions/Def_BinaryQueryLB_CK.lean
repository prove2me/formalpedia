-- Prove2me | Definitions.Def_BinaryQueryLB_CK
-- name    : BinaryQueryLB_CK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:35.338402+00:00
-- url     : https://prove2.me/theorems/7586684d-62f9-4c9e-b270-f94493113888
-- title:
--   The constant $C_K=128(\Gamma+1)^2$
-- statement:
--   The constant $C_K=128(\Gamma+1)^2$, which equals $1\,305\,728$ for $\Gamma=100$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §3, p.15

import Mathlib
import Definitions.Def_BinaryQueryLB_GammaConst

namespace BinaryQueryLB

/-- **The constant `C_K = 128(Γ + 1)^2`.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §3, p.15: "Recall that `CK = 128(Γ + 1)^2`."
(With `Γ = 100` this is `1 305 728`.) -/
noncomputable def CK : ℝ := 128 * (GammaConst + 1) ^ 2

end BinaryQueryLB


