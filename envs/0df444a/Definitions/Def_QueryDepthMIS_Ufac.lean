-- Prove2me | Definitions.Def_QueryDepthMIS_Ufac
-- name    : QueryDepthMIS_Ufac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:26:32.892436+00:00
-- url     : https://prove2.me/theorems/e817e996-67ab-492b-afcf-6a75b7c01dfd
-- title:
--   The factor $U_{L,h,\alpha,\beta,\epsilon}$
-- statement:
--   $$
--   U_{L,h,\alpha,\beta,\epsilon} = (1 - \epsilon)^{L/2 - 1 - 2b - h}\,(1 - \beta)^{-L}\,(en)^2\,(1 - \alpha)^{-L}.
--   $$
--   **Formalization Note** The exponent $L/2 - 1 - 2b - h$ is a real number, possibly negative, and the power is the real power; $b$ and $n$ are explicit arguments.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.16

import Mathlib

set_option autoImplicit false

namespace QueryDepthMIS

/-- The factor `U_{L,h,α,β,ε}` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.16): "Denote by U_{L,h,α,β,ϵ} the term
(1 − ϵ)^{L/2−1−2b−h}(1 − β)^{−L}(en)²(1 − α)^{−L}."

**Formalization Note** The exponent `L/2 − 1 − 2b − h` is a real number, possibly negative, and
the power is `Real.rpow` (base `1 − ε > 0` in every use); `(1 − β)^{−L}` and `(1 − α)^{−L}` are
inverses of natural powers. `b` and `n` are explicit arguments. -/
noncomputable def Ufac (L h b : ℕ) (α β ε : ℝ) (n : ℕ) : ℝ :=
  (1 - ε) ^ ((L : ℝ) / 2 - 1 - 2 * (b : ℝ) - (h : ℝ)) * ((1 - β) ^ L)⁻¹ *
    (Real.exp 1 * n) ^ 2 * ((1 - α) ^ L)⁻¹

end QueryDepthMIS


