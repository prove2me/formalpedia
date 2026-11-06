-- Prove2me | Definitions.Def_LawLocalComp_cellMean
-- name    : LawLocalComp_cellMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:29.547252+00:00
-- url     : https://prove2.me/theorems/75d228f6-f79b-469e-9967-9f08fae54faf
-- title:
--   Conditional mean of a cell
-- statement:
--   For a labelling of the atoms of $X$ by integers (cells), the cell mean of the cell $k$ is $\mathbb E[X\mid \text{cell}(X)=k]$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §3, p.5; Lemma 7.2, p.13

import Mathlib
import Definitions.Def_LawLocalComp_Law

namespace LawLocalComp

/-- **The conditional mean of a cell.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §3, p.5 ("Each label retains its mass and conditional mean"); Lemma 7.2, p.13 ("Replace the full
value b + R by its cell mean").

For a cell labelling `key : ℝ → ℤ`, `cellMean X key k = E[X | key X = k]`. -/
noncomputable def cellMean (X : Law) (key : ℝ → ℤ) (k : ℤ) : ℝ :=
  (∑ x ∈ X.w.support with key x = k, x * X.w x) / ∑ x ∈ X.w.support with key x = k, X.w x

end LawLocalComp


