-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_LineAnchorGCD
-- name    : WeierstrassEllipticZeta_LineAnchorGCD
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-22T17:11:57.129229+00:00
-- url     : https://prove2.me/theorems/e5cd2b8e-8ee6-4376-97ff-8de469d82e1a
-- title:
--   GCD polynomials and line candidates without intercept witnesses
-- statement:
--   For fixed elliptic coordinate b and line slope alpha, let the intercept slice at additive coordinate t be the polynomial beta -> F(t,b,alpha*t+beta), using the existing regularized evaluation and anchorSlice definition.
--
--   Define lineAnchorGCD to be zero when the existing first-nonzero-slice obstruction is zero. Otherwise it is the normalized GCD of the m+n+1 intercept slice polynomials at t=0,...,m+n. The zero convention agrees with the existing lineAnchorRoots definition, which gives an empty line-root set when the obstruction vanishes; that degeneracy is represented by the whole-fibre branch.
--
--   GCDAnchorCandidate retains the origin tag and the finite whole-fibre list Z. Its line branch contains a period-pair index and a coordinate b in the supplied region K satisfying positive natural degree of lineAnchorGCD. There is no chosen intercept in this branch. gcdAnchorLocus forgets the degree test and retains the exact underlying point, fibre or period-pair line candidate.
--
--   The definition does not itself assert that a positive-degree GCD is equivalent to a valid line anchor; the accompanying theorem proves that fact, the exact root-set equality and the degree bound. Line coordinates can still vary continuously over K, so this is not a finite global candidate type.
-- source:
--   Derived GCD criterion for line anchors in the A.1 frontier https://prove2.me/theorems/0d893d2a-f5ba-4f36-a984-39565ad59d87. For fixed b and slope alpha, take the GCD of the intercept slices F(j,b,alpha*j+beta), j=0,...,m+n, with the existing zero-obstruction case assigned zero. The exact tested intercept set equals its distinct root set. The GCD divides the nonzero obstruction, so its degree is at most n. The fundamental theorem of algebra makes positive degree equivalent to existence of a tested intercept. Primary pinned sources: Finset.dvd_gcd_iff and Finset.gcd_dvd, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/GCDMonoid/Finset.lean; Polynomial.mem_roots and Polynomial.card_roots', https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean; and Complex.exists_root, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/Polynomial/Basic.lean. The cost frontier replaces its chosen intercept by the positive-degree test, preserving the exact candidate, coordinate, class count, degree, chart point, chart cost and C. This is a derived supporting criterion. Mission context: the elementary line case in Appendix A of Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. Line coordinates remain potentially continuous. The existing degree-n bound and integer-search bound are unchanged; the global geometric cost estimate remains Open. No numerical root-finding algorithm is claimed.

import Definitions.Def_WeierstrassEllipticZeta_FibreEnumeratedAnchors
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Content

noncomputable section
open scoped Classical
namespace WeierstrassEllipticZeta

/-- A zero obstruction is assigned zero, since that branch is handled by a
whole fibre. Otherwise take the GCD of all canonical line-sample polynomials. -/
def lineAnchorGCD (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (b α : ℂ) : Polynomial ℂ :=
  if anchorObstruction S Q m b α = 0 then 0 else
    (Finset.range (m + n + 1)).gcd (fun j : ℕ => anchorSlice S Q b α j)

/-- A line is represented by a positive-degree GCD test, without a chosen
intercept. The whole-fibre coordinate is still chosen from the supplied list. -/
abbrev GCDAnchorCandidate (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) :=
  Unit ⊕ (↥Z ⊕ ((p : ↥(periodPairCandidates Λ X)) ×
    {b : K // 0 < (lineAnchorGCD S Q m n b.val (periodPairSlope Λ η X p)).natDegree}))

/-- Forget the GCD test and retain the exact point, fibre or period-pair index. -/
def gcdAnchorLocus (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) :
    GCDAnchorCandidate Λ η X S Q m n K Z → FiniteLocusCandidate Λ X
  | .inl _ => .inl ()
  | .inr (.inl _) => .inr (.inl ())
  | .inr (.inr p) => .inr (.inr p.1)

end WeierstrassEllipticZeta


