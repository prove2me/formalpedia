-- Prove2me | Definitions.Def_SpencerEight_signedSum
-- name    : SpencerEight_signedSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:37.309201+00:00
-- url     : https://prove2.me/theorems/72bab824-183c-408d-9906-374f28d0c866
-- title:
--   Linear matrix series $G(x)=\sum_i x_iB_i$
-- statement:
--   For matrices $(B_i)_{i\in S}$ and real coefficients $x$, put
--   $$G(x):=\sum_{i\in S}x_iB_i.$$
--   The coefficient vector may be a full signing, a partial signing with entries in $\{-1,0,1\}$, or a Gaussian vector.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.43, p.105 (PDF p.105)

import Mathlib

namespace SpencerEight

/-- The linear matrix series `G(x) := ∑ᵢ xᵢ Bᵢ` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.43, p.105 (PDF p.105)), for real coefficients `x`: sign vectors, partial signings and Gaussian vectors alike. -/
def signedSum {ι d : Type*} [Fintype ι] (B : ι → Matrix d d ℝ) (x : ι → ℝ) : Matrix d d ℝ :=
  ∑ i, x i • B i

end SpencerEight


