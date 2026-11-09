-- Prove2me | Definitions.Def_RSCapacity_ListDecoding_Counting
-- name    : RSCapacity_ListDecoding_Counting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:15.996101+00:00
-- url     : https://prove2.me/theorems/93d7a51d-9896-411c-92de-7ed23f1e064c
-- title:
--   Weighted simplex and monomial counting data
-- statement:
--   For a positive integer $d$ and a real cutoff $W$, define the discrete and continuous weighted simplexes
--   $$\Lambda_d(W)=\{b\in\mathbb N^d:\textstyle\sum_{i=1}^d i b_i\le W\},\qquad
--   \lambda_d(W)=\{x\in\mathbb R_{\ge0}^d:\textstyle\sum_{i=1}^d i x_i\le W\}.$$
--   The volume is ordinary $d$-dimensional product Lebesgue measure. For $W\ge0$, the uniform coordinate and total means are the finite sums divided by $|\Lambda_d(W)|$. Write $H_d=\sum_{i=1}^d1/i$. For positive integers $k,D$, the monomial count is the cardinality of the pairs $(a,b)\in\mathbb N^2$ with $a+kb<D$.
--
--   These definitions share the source's counting objects across both simplex estimates and the interpolation bookkeeping. The published general weighted domains are specialized, rather than redeclared.
--
--   **Formalization Note** Coordinate $i$ in `Fin d` corresponds to the printed coordinate $i+1$. The finite bounding box for monomials is exact on the stipulated positive-$k$ domain. Means on an empty set have Lean's default zero but no theorem uses them there; all real measures used here are finite.
-- source:
--   Prahladh Harsha, Mrinal Kumar, Ramprasad Saptharishi, STOC 2027 submission #495 (October 2026), §2 p.7; §4 pp.14–15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/495.pdf

import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains
import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion

open scoped BigOperators

namespace RSCapacity.ListDecoding

/-- Source §4, p.14: coordinate i represents the source coordinate i+1. -/
noncomputable def latticeSimplex (d : ℕ) (W : ℝ) : Finset (Fin d → ℕ) :=
  OAI.PiExponent.realWeightedSimplex (fun i => (i.val + 1 : ℕ)) W

def continuousSimplex (d : ℕ) (W : ℝ) : Set (Fin d → ℝ) :=
  OAI.PiExponent.DeterminantContradiction.weightedSimplexRegion
    (fun i => (i.val + 1 : ℕ)) W

/-- Actual product Lebesgue measure, converted only for bounded simplexes. -/
noncomputable def simplexVolume (d : ℕ) (W : ℝ) : ℝ :=
  (MeasureTheory.volume (continuousSimplex d W)).toReal

noncomputable def coordinateMean (d : ℕ) (W : ℝ) (i : Fin d) : ℝ :=
  (∑ b ∈ latticeSimplex d W, (b i : ℝ)) / (latticeSimplex d W).card

noncomputable def totalMean (d : ℕ) (W : ℝ) : ℝ :=
  (∑ b ∈ latticeSimplex d W, ∑ i : Fin d, (b i : ℝ)) /
    (latticeSimplex d W).card

noncomputable def harmonic (d : ℕ) : ℝ := ∑ i : Fin d, (1 : ℝ) / (i.val + 1 : ℕ)

/-- Fact 2.1: strict cutoff, nonnegative exponents; the bounding box loses
no point when k is positive. -/
def bivariateMonomials (k D : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range D).product (Finset.range D)).filter fun ab => ab.1 + k * ab.2 < D

end RSCapacity.ListDecoding


