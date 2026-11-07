-- Prove2me | Definitions.Def_UnionVolEst_AlponaState
-- name    : UnionVolEst_AlponaState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:02:49.656019+00:00
-- url     : https://prove2.me/theorems/f7734139-7269-4f2c-bfe7-d194acf4adf3
-- title:
--   State of Alpona between bodies
-- statement:
--   The state of Alpona after processing some of the bodies consists of the multiset $X$ of stored points, the sampling intensity $p = 2^{-\ell}$ (recorded by the exponent $\ell$, since $p$ starts at $1$ and is only halved), and the numbers of calls made so far to ComputeVolume and to GenerateSamples.
--
--   **Formalization Note** The multiset is a `List`.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, Algorithm 1, p.15 (PDF p.17)

import Mathlib

namespace UnionVolEst

/-- The state of Algorithm 1 (Alpona) between two bodies (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, printed p.15, PDF p.17):
the multiset `X` of stored points, the sampling intensity `p = 2^{−level}`, and the numbers of
calls made so far to ComputeVolume and to GenerateSamples.

**Formalization Note** The multiset is a `List` (order irrelevant). Since `p` starts at `1` and is
only ever halved, it is recorded by the exponent `level`. -/
structure AlponaState (n : ℕ) where
  /-- the multiset `X` of stored points -/
  X : List (EuclideanSpace ℝ (Fin n))
  /-- `p = 2^{−level}` -/
  level : ℕ
  /-- calls to ComputeVolume so far -/
  volCalls : ℕ
  /-- calls to GenerateSamples so far -/
  sampCalls : ℕ

end UnionVolEst


