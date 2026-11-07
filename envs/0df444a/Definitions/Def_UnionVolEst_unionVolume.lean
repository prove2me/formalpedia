-- Prove2me | Definitions.Def_UnionVolEst_unionVolume
-- name    : UnionVolEst_unionVolume
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:02:46.353972+00:00
-- url     : https://prove2.me/theorems/9343ede8-2a70-40b4-a99a-85251fb6e137
-- title:
--   Volume of the union $F_0 = \mathrm{Vol}(\bigcup_j K_j)$
-- statement:
--   For sets $K_1,\dots,K_M\subseteq\mathbb R^n$,
--   $$
--   F_0 := \mathrm{Vol}\Big(\bigcup_{j=1}^M K_j\Big),
--   $$
--   the quantity Alpona estimates.
--
--   **Formalization Note** Lebesgue measure on $\mathbb R^n$ = `EuclideanSpace ℝ (Fin n)`, read as a real number; every result assumes each $K_j$ has finite volume.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.1, p.17 (PDF p.19)

import Mathlib

open MeasureTheory

namespace UnionVolEst

/-- The volume of the union, `F₀ := Vol(⋃_{j=1}^M K_j)` (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.1, printed p.17, PDF p.19).

**Formalization Note** Lebesgue measure on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, read in `ℝ` by
`ENNReal.toReal`; every result using it assumes each `K_i` has finite volume, so the union has
finite volume and nothing is lost. -/
noncomputable def unionVolume {n M : ℕ} (K : Fin M → Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  (volume (⋃ i, K i)).toReal

end UnionVolEst


