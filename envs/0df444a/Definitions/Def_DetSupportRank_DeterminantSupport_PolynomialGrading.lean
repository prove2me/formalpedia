-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_PolynomialGrading
-- name    : DetSupportRank_DeterminantSupport_PolynomialGrading
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:11.707295+00:00
-- url     : https://prove2.me/theorems/0b297daa-58e3-4aa1-a4dc-e58cca6df775
-- title:
--   Weighted monomial degrees and homogeneity
-- statement:
--   Assign to every variable $x_v$ an integer multidegree $p_v\in\mathbb Z^d$. A monomial and a homogeneous polynomial have degrees specified by
--   $$\deg(x^e)=\sum_v e_vp_v,\qquad f\text{ homogeneous of degree }u\iff\operatorname{supp}(f)\subseteq\{e:\deg(x^e)=u\}.$$
--   Zero is homogeneous of every degree. A negative degree contains no nonzero monomial when all variable weights are nonnegative.
--
--   This is the reusable polynomial-grading object used by both degree relations and shifted modules; it does not assign a default degree to zero.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §2, homogeneous polynomials, p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Mathlib

noncomputable section

namespace DetSupportRank.DeterminantSupport

/-- Integer multidegree of a monomial, for arbitrary variable weights. -/
def monomialDegree {V D : Type*} (p : V → D → ℤ) (e : V →₀ ℕ) : D → ℤ :=
  e.sum fun v k => (k : ℤ) • p v

/-- Zero is homogeneous in every degree, including degrees with negative coordinates. -/
def Homogeneous {K V D : Type*} [Field K] (p : V → D → ℤ)
    (u : D → ℤ) (f : MvPolynomial V K) : Prop :=
  ∀ e ∈ f.support, monomialDegree p e = u

end DetSupportRank.DeterminantSupport


