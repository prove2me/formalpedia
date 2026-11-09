-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_DegreeVarieties
-- name    : DetSupportRank_DeterminantSupport_DegreeVarieties
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:00.637739+00:00
-- url     : https://prove2.me/theorems/4c764535-ac1a-4ff2-9b5e-f69dbfdb2fd1
-- title:
--   Degree varieties and hyperplane covering rank
-- statement:
--   For every positive integer $r$, the degree variety is
--   $$X_r(f)=\{y\in\mathbb C^d:\ \forall a\sim_f b,\ \sum_i(a_i\cdot y)^r=\sum_i(b_i\cdot y)^r\}.$$
--   The quantifier includes every finite tuple size. For a subset $S$ of rows, its hyperplane is $\{y:\sum_{i\in S}y_i=0\}$. The covering rank $\rho(f)$ is the infimum of positive integers $r$ such that $X_r(f)$ is covered by $r$ such hyperplanes for nonempty proper row subsets. Repetitions are allowed.
--
--   These are the equation-defined varieties and actual coverings of the source. The dot product has no complex conjugation, and an empty set of covering witnesses gives infinity.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Definition 3.4, p.6; Definition 3.7, p.7, p. 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_DegreeRelations

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport

/-- Definition 3.4, p.6. Only r ≥ 1 is used in the source. Every finite degree relation is tested. -/
def degreeVariety {K : Type*} [Field K] {d m : ℕ}
    (f : MvPolynomial (Fin d × Fin m) K) (r : ℕ) : Set (Fin d → ℂ) :=
  {y | ∀ N : ℕ, ∀ a b : Fin N → Fin d → ℕ, DegreeRelation f a b →
    ∑ i, degreeDot (a i) y ^ r = ∑ i, degreeDot (b i) y ^ r}

/-- The subset-sum hyperplanes of Definition 3.7, with no complex conjugation. -/
def subsetHyperplane {d : ℕ} (S : Finset (Fin d)) : Set (Fin d → ℂ) :=
  {y | ∑ i ∈ S, y i = 0}

/-- Definition 3.7, p.7. Infimum in ℕ∞, with ∞ for an empty witness set. -/
def coveringRank {K : Type*} [Field K] {d m : ℕ}
    (f : MvPolynomial (Fin d × Fin m) K) : ℕ∞ :=
  ⨅ r : {r : ℕ // 1 ≤ r ∧ ∃ S : Fin r → Finset (Fin d),
      (∀ i, (S i).Nonempty ∧ S i ≠ Finset.univ) ∧
      degreeVariety f r ⊆ {y | ∃ i, y ∈ subsetHyperplane (S i)}}, (r.val : ℕ∞)

end DetSupportRank.DeterminantSupport


