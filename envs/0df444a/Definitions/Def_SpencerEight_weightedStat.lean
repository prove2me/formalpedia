-- Prove2me | Definitions.Def_SpencerEight_weightedStat
-- name    : SpencerEight_weightedStat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:39.362715+00:00
-- url     : https://prove2.me/theorems/8007c801-a8f3-4800-8e18-7bc7a0405ef0
-- title:
--   Weighted statistic $F_k(X)$ of Lemma 8.48
-- statement:
--   For a matrix $T$, an integer $k$ and coefficients $a_j$, put
--   $$F_k(X):=a_1\operatorname{tr}[T^{2k}X^2]+\sum_{j=2}^{d}a_j\operatorname{tr}[X^{2j}].$$
--   The envelope $T$ is retained in the quadratic term only.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.48, p.108 (PDF p.108)

import Mathlib

namespace SpencerEight

/-- The weighted statistic of Lemma 8.48 (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.108 (PDF p.108)): `F_k(X) := a_{k,1} tr[T^{2k} X²] + ∑_{j=2}^{d_k} a_{k,j} tr[X^{2j}]`. -/
def weightedStat {d : Type*} [Fintype d] [DecidableEq d] (T : Matrix d d ℝ) (k deg : ℕ) (a : ℕ → ℝ)
    (X : Matrix d d ℝ) : ℝ :=
  a 1 * (T ^ (2 * k) * X ^ 2).trace + ∑ j ∈ Finset.Icc 2 deg, a j * (X ^ (2 * j)).trace

end SpencerEight


