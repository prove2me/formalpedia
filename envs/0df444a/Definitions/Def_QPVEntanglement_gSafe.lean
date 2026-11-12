-- Prove2me | Definitions.Def_QPVEntanglement_gSafe
-- name    : QPVEntanglement_gSafe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:26:58.556939+00:00
-- url     : https://prove2.me/theorems/63f18f37-4acc-4957-bdfa-072363fa5e4f
-- title:
--   The functions $g$, $f$ and $g_{\mathrm{safe}}$
-- statement:
--   With $h$ the binary entropy in bits ($h(0)=h(1)=0$), $g(\epsilon)=\epsilon\log_2 3+h(\epsilon)$, $f(\epsilon)=\epsilon\log_2 3+2h(\epsilon)$, and
--
--   $$g_{\mathrm{safe}}(\epsilon)=\begin{cases}g(\epsilon),&\epsilon\le 3/4,\\ g(3/4),&\epsilon>3/4.\end{cases}$$
--
--   They are the loss terms of Lemmas 3 and 7 and Theorem 6.
--
--   **Formalization Note** $h$ is the published `QAlgorithms.binEntropy2`.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), §3, eq. (2), p.26

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

set_option autoImplicit false

namespace QPVEntanglement

/-- `g(ϵ) = ϵ log₂ 3 + h(ϵ)` (§3, p.26), `h` the binary entropy in bits
(`QAlgorithms.binEntropy2`, published; `h(0) = h(1) = 0`). -/
noncomputable def gFun (ε : ℝ) : ℝ := ε * Real.logb 2 3 + QAlgorithms.binEntropy2 ε

/-- `f(ϵ) = ϵ log₂ 3 + 2h(ϵ)` (§3, p.26). -/
noncomputable def fFun (ε : ℝ) : ℝ := ε * Real.logb 2 3 + 2 * QAlgorithms.binEntropy2 ε

/-- **The concave non-decreasing extension `g_safe`** (§3, eq. (2), p.26). Behera–Goyal,
arXiv:2609.39234 (sha256 bdf2928d…), eq. (2), p.26:
`g_safe(ϵ) = g(ϵ)` for `ϵ ≤ 3/4` and `g(3/4)` for `ϵ > 3/4`. -/
noncomputable def gSafe (ε : ℝ) : ℝ := if ε ≤ 3 / 4 then gFun ε else gFun (3 / 4)

end QPVEntanglement


