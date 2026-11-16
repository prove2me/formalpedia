-- Prove2me | Definitions.Def_MaxCompForest_Supplement_dNormSq
-- name    : MaxCompForest_Supplement_dNormSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:08:14.935017+00:00
-- url     : https://prove2.me/theorems/d82aa3f5-32e2-43fd-82b5-c6fb8e65e86d
-- title:
--   Squared $D$-norm $\|g\|_D^2$
-- statement:
--   For masses $(d_v)_{v\in V}$ (the weighted degrees of a graph) and a signal $g\in\mathbb R^V$, the **squared $D$-norm** is
--
--   $$\|g\|_D^2=\sum_{v\in V} d_v\,g_v^2 .$$
--
--   It is the loss of the graph denoising model of Section 5: errors at high-degree vertices count more.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), §5, p.28 (PDF p.30), "measure squared D-error"

import Mathlib
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {V : Type*} [Fintype V]

/-- **The squared `D`-norm** `‖g‖²_D = ∑_v d_v g_v²` of a vertex signal, for a mass vector `W` (the degrees `d`).
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), §5, p.28 ("measure squared D-error"). -/
def dNormSq (W : V → ℝ) (g : V → ℝ) : ℝ := ∑ v, W v * g v ^ 2

end MaxCompForest.Supplement


