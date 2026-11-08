-- Prove2me | Definitions.Def_SpencerEight_df
-- name    : SpencerEight_df
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:58.387804+00:00
-- url     : https://prove2.me/theorems/0784cb2b-b38b-454e-8038-7a94d85269b1
-- title:
--   Double factorial $\mathrm{df}$
-- statement:
--   $\mathrm{df}(r):=(2r-1)!!$ for $r\ge1$, and $\mathrm{df}(0):=1$. These are the even moments of a standard Gaussian.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Definition 8.10, p.75 (PDF p.75)

import Mathlib
open scoped Nat

namespace SpencerEight

/-- `df(r) := (2r − 1)!!` for `r ≥ 1`, and `df(0) := 1` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Definition 8.10, p.75 (PDF p.75)). -/
noncomputable def df : ℕ → ℝ
  | 0 => 1
  | r + 1 => ((2 * (r + 1) - 1)‼ : ℕ)

end SpencerEight


