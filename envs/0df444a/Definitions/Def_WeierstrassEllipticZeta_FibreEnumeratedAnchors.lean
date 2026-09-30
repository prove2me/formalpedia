-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_FibreEnumeratedAnchors
-- name    : WeierstrassEllipticZeta_FibreEnumeratedAnchors
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-22T16:21:33.49211+00:00
-- url     : https://prove2.me/theorems/f7eb6702-4580-4dd7-b27f-6ed97ebc0ff5
-- title:
--   Anchors with a finite list of whole-fibre coordinates
-- statement:
--   Given the existing finite point/fibre/period-pair locus candidates, a region K in C and a finite list Z of whole-fibre coordinates, the fibre-enumerated anchor type has three branches:
--
--   - A unit tag for the origin point.
--   - A coordinate in the finite set Z for a whole-fibre candidate.
--   - A period-pair slope, a coordinate b in K and an intercept in the existing tested line-root set at that b and slope.
--
--   The associated map returns the underlying finite locus candidate: point, fibre or the same period-pair line index. The definition alone does not assert that Z is the correct list. The complete theorem supplies the exact condition b in Z iff b lies in K and passes every canonical fibre test. Under that condition and 0 in K, the new type represents exactly the same underlying candidate predicates as the old bounded-anchor type.
--
--   Only the whole-fibre coordinate is enumerated by Z. The line branch still contains a potentially continuous choice of b in K, and the whole candidate type is not asserted to be finite.
-- source:
--   Derived finite whole-fibre enumeration for the A.1 frontier https://prove2.me/theorems/cd5e1c96-23d5-494e-ba7b-70a81e2a670c. For a nonzero diagonal pullback, one of the (m+1)(n+1) integer fibre sample functions b -> F(i,b,j) is nonzero. Otherwise the Proved finite interpolation theorem 0d85f1e1-6c11-46f4-8278-88c0ac3aa265 would force every fibre, and hence the diagonal, to vanish. That sample function is entire. Every whole-fibre coordinate is among its zeros, of which only finitely many lie in a compact region. Primary analytic sources: pinned Mathlib's AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/IsolatedZeros.lean, and IsCompact.finite_sdiff_of_mem_codiscreteWithin, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/DiscreteSubset.lean. The new finite list replaces the whole-fibre coordinate in an exact candidate model; line coordinates still range over the compact region. Both frontier directions preserve the exact finite locus candidate, class count, degree, chart point, chart cost and C. Mission context: the regularized exponential map at the beginning of Appendix A in Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. This enumeration is derived here, not quoted as the paper's global zero estimate. No cardinality bound in terms of m,n or root-isolation algorithm is proved. The global uniform cost estimate remains Open; the integer-search bound is unchanged.

import Definitions.Def_WeierstrassEllipticZeta_FiniteAnchorCandidates

noncomputable section
open scoped Classical
namespace WeierstrassEllipticZeta

/-- Anchors with the whole-fibre coordinate chosen from a supplied finite list.
Line coordinates still range over the supplied compact region. -/
abbrev FibreEnumeratedAnchorCandidate (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) :=
  Unit ⊕ (↥Z ⊕ ((p : ↥(periodPairCandidates Λ X)) × (b : K) ×
    ↥(lineAnchorRoots S Q m n b.val (periodPairSlope Λ η X p))))

/-- The underlying point, fibre, or period-pair line candidate. -/
def fibreEnumeratedAnchorLocus (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) :
    FibreEnumeratedAnchorCandidate Λ η X S Q m n K Z → FiniteLocusCandidate Λ X
  | .inl _ => .inl ()
  | .inr (.inl _) => .inr (.inl ())
  | .inr (.inr p) => .inr (.inr p.1)

end WeierstrassEllipticZeta


