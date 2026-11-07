-- Prove2me | Definitions.Def_SmoothBerr_stdGaussianVec
-- name    : SmoothBerr_stdGaussianVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:06.553202+00:00
-- url     : https://prove2.me/theorems/bbec1600-c834-4b76-ac09-5d695bb95360
-- title:
--   Standard Gaussian vector law $\mathcal N(0,I_k)$
-- statement:
--   The **standard Gaussian law** on $\mathbb R^k$ is the law $\mathcal N(0,I_k)$ of a vector $z=(z_1,\dots,z_k)$ whose coordinates are independent standard normal variables:
--   $$
--   \mathcal N(0,I_k)=\bigotimes_{i=1}^k\mathcal N(0,1).
--   $$
--   It is the law of "a standard Gaussian $z$" in Anderson's inequality (Imported Lemma 5.6), and the row law of a Gaussian matrix.
--
--   **Formalization Note** The product measure of `gaussianReal 0 1` over `Fin k`, on `Fin k → ℝ` with its product σ-algebra; it is a probability measure (registered as an instance).
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Imported Lemma 5.6, p.14 ("z is standard Gaussian"); §5, p.12 ("g ∼ N(0, I_n)")

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SmoothBerr

/-- The law `N(0, I_k)` of a standard Gaussian vector in `ℝᵏ`: independent `N(0,1)` coordinates
(Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of
adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Imported Lemma 5.6, p.14:
"z is standard Gaussian"; §5, p.12: "g ∼ N(0, I_n)").

**Formalization Note** The product of `gaussianReal 0 1` over `Fin k`, on `Fin k → ℝ` with the
product σ-algebra; it is the row law of the published `GaussianMatrix.gaussianMatrix`. -/
noncomputable def stdGaussianVec (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ : Fin k => gaussianReal 0 1

instance stdGaussianVec_isProbabilityMeasure (k : ℕ) :
    IsProbabilityMeasure (stdGaussianVec k) := by
  unfold stdGaussianVec; infer_instance

end SmoothBerr


