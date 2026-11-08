-- Prove2me | Definitions.Def_SpencerEight_reserve
-- name    : SpencerEight_reserve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:18.526003+00:00
-- url     : https://prove2.me/theorems/81557253-33c1-4870-9bef-5cb79a2c3855
-- title:
--   Reserve $C_i$
-- statement:
--   $C_i:=C_0-\sum_{h=1}^iL_h$, the headroom left after $i$ partial signings of costs $L_h\sqrt n$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.45, p.106 (PDF p.106)

import Mathlib

namespace SpencerEight

/-- The reserve `C_i := C₀ − ∑_{h=1}^i L_h` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.45, p.106 (PDF p.106)). -/
def reserve (C0 : ℝ) (L : ℕ → ℝ) (i : ℕ) : ℝ := C0 - ∑ h ∈ Finset.Icc 1 i, L h

end SpencerEight


