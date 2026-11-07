-- Prove2me | Definitions.Def_SparseHistComm_prior
-- name    : SparseHistComm_prior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:49.447991+00:00
-- url     : https://prove2.me/theorems/351249d2-9528-4e88-8196-2f34a84408a4
-- title:
--   Uniform prior mass $1/\binom dk$ on $k$-subsets
-- statement:
--   The analysis of Section IV draws $X_1,\dots,X_n$ independently and uniformly over binary vectors with **exactly** $k$ active coordinates. Each $k$-subset of $\{1,\dots,d\}$ has prior mass
--   $$
--   \pi(x) = \binom dk^{-1}.
--   $$
--
--   **Formalization Note** The mass is an extended nonnegative real; every use sums it over the $k$-subsets (or $n$-tuples of them), so the value $\infty$ that $1/0$ takes when $k > d$ never contributes (there are then no $k$-subsets).
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section IV, p.8

import Mathlib
open scoped ENNReal

namespace SparseHistComm

/-- The mass `1 / C(d, k)` of each support under the analysis prior of Section IV (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), p.8: "Let
X₁, …, Xₙ be independent and uniform over binary vectors with exactly k active coordinates").

**Formalization Note** The prior of one user is uniform on `powersetCard k` of `Fin d`; every use
sums `prior d k` over that set (or over `n`-tuples of its elements), so the value `⊤` of the
inverse when `k > d` never contributes (the set is then empty). -/
noncomputable def prior (d k : ℕ) : ℝ≥0∞ :=
  ((d.choose k : ℕ) : ℝ≥0∞)⁻¹

end SparseHistComm


