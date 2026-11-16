-- Prove2me | Definitions.Def_GaussPolyReg_Approx_Supplement_Graded
-- name    : GaussPolyReg_Approx_Supplement_Graded
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:26:07.831781+00:00
-- url     : https://prove2.me/theorems/6f58ca91-f632-47e6-abfa-ae98782193bc
-- title:
--   Countable graded projections and bounded joint-law sets
-- statement:
--   Let $I=\mathbb N_{>0}\times\mathbb N$, with independent standard Gaussian coordinates $Z_{r,i}$ and grade $g(r,i)=r$. The underlying measure and the closed Hermite chaos $H_d^{\mathrm{gr}}$ are imported from the published base definition. For every $f\in L^2(\gamma_I)$, $\Pi_d f$ is its orthogonal projection onto that closed chaos.
--
--   For a finite degree vector $(d_1,\ldots,d_k)$ define
--
--   $$\mathcal K_d=\{\operatorname{Law}(p_1,\ldots,p_k):p_i\in H_{d_i}^{\mathrm{gr}},\ \mathbb E p_i^2\le1\text{ for every }i\}.$$
--
--   The set lives in the space of Borel probability measures on $\mathbb R^k$ with the weak topology. The probability-measure wrapper has underlying measure exactly the published Euclidean vectorLaw of the tuple. Dependence among coordinates is unrestricted; the bounds are individual, not a bound on their sum. Degree zero and the empty finite tuple are included. This interface supplies the projections and the precise compactness set in Theorem 3.8 without assuming compactness.
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), §2, p.3, (2.1); Theorem 3.8, p.11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Chaos

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section

namespace GaussPolyReg.Approx.Supplement

/-- Countably many independent coordinates of every positive grade (§2, p.3). -/
abbrev GradedIndex := ℕ+ × ℕ
abbrev GradedPoint := GradedIndex → ℝ
abbrev GradedL2 := GaussianL2 GradedIndex

def coordinateGrade (i : GradedIndex) : ℕ := i.1

/-- Orthogonal projection to the published closed Hermite span, now for any grades. -/
def gradedProjection {I : Type*} (g : I → ℕ) (d : ℕ)
    (f : GaussianL2 I) : GaussianL2 I :=
  letI : (gradedChaos g d).HasOrthogonalProjection := by
    unfold gradedChaos
    infer_instance
  ((gradedChaos g d).orthogonalProjectionOnto f : GaussianL2 I)

/-- Full joint-law set, with an individual second-moment bound on each coordinate.
The measure is the published vectorLaw on the published Euclidean Vec. -/
def boundedJointLaws {k : ℕ} (d : Fin k → ℕ) : Set (ProbabilityMeasure (Vec k)) :=
  {ν | ∃ p : Fin k → GradedL2,
    (∀ i, p i ∈ gradedChaos coordinateGrade (d i) ∧ ‖p i‖ ^ 2 ≤ 1) ∧
    (ν : Measure (Vec k)) = vectorLaw p}

end GaussPolyReg.Approx.Supplement


