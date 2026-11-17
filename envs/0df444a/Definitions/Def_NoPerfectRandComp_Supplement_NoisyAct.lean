-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_NoisyAct
-- name    : NoPerfectRandComp_Supplement_NoisyAct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:16:00.599851+00:00
-- url     : https://prove2.me/theorems/18e57cf8-00a7-45db-9576-6bc38164e828
-- title:
--   Step of a noisy query algorithm
-- statement:
--   One step of a noisy query algorithm: a **noisy query** to $x_i$ with correlation $\gamma\in[0,1]$, which returns $x_i$ with probability $(1+\gamma)/2$ (otherwise $\neg x_i$) and costs $\gamma^2$; an internal fair coin flip, which costs nothing; or stopping with an output bit. Exact queries have correlation $1$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4, p.11

import Mathlib

namespace NoPerfectRandComp

namespace Supplement

/-- One step of a noisy query algorithm (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4, p.11): make a noisy query to `x_i`
with correlation `γ ∈ [0, 1]` (it returns `x_i` with probability `(1 + γ)/2`, else `¬x_i`, and
costs `γ²`), flip a fair internal coin (cost `0`), or stop with an output bit. -/
inductive NoisyAct (ι : Type) where
  | query (i : ι) (γ : Set.Icc (0 : ℝ) 1)
  | coin
  | stop (b : Bool)

end Supplement

end NoPerfectRandComp


