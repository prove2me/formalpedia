-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_UniformBias
-- name    : DetSupportRank_DeterminantSupport_Supplement_UniformBias
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:07:07.527781+00:00
-- url     : https://prove2.me/theorems/57caa688-be45-4d47-aa3f-a5c2c300fd72
-- title:
--   Uniform output-probability bias
-- statement:
--   For a function $T:A\to F$ on a finite set, define
--   $$\operatorname{bias}(T)=\frac{|\{x:T(x)=0\}|-|\{x:T(x)=1\}|}{|A|}.$$
--   The two cardinalities are converted to real numbers before subtraction. On the source domain $A$ is the nonempty space of all entries of a multilinear input, so the denominator is positive. The extension on an empty input set is zero. This generic definition is independent of any special polynomial or rank estimate.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §1, definition of bias, p. 2 (PDF p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Mathlib

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- Uniform probability of output zero minus that of output one, §1, p.2.
The subtraction is in ℝ, before normalization; no truncated cardinal subtraction. -/
def uniformBias {A F : Type*} [Fintype A] [Zero F] [One F] (T : A → F) : ℝ := by
  classical
  exact (((Finset.univ.filter (fun x => T x = 0)).card : ℝ) -
    ((Finset.univ.filter (fun x => T x = 1)).card : ℝ)) / (Fintype.card A : ℝ)
end DetSupportRank.DeterminantSupport.Supplement


