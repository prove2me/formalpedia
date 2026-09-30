-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_SparseLineAnchorGCD
-- name    : WeierstrassEllipticZeta_SparseLineAnchorGCD
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-22T18:23:27.16782+00:00
-- url     : https://prove2.me/theorems/276dc40e-441a-4dcc-b1f2-9a3cc2d3f1d9
-- title:
--   Minimum-cardinality slice families for sparse line-anchor GCDs
-- statement:
--   For a finite family of polynomials, polynomialGCDCore chooses a subfamily of smallest cardinality having exactly the same normalized GCD. Such a subfamily always exists because the full family is admissible. The definition selects among the finite powerset; it makes no efficiency or computability claim for complex coefficients.
--
--   For the existing line-anchor slices p_j(beta)=F(j,b,alpha*j+beta), lineAnchorGCDCore applies this construction to j=0,...,m+n when the existing obstruction is nonzero. In the zero-obstruction case it returns the empty family, consistently with the earlier convention assigning the line GCD zero. sparseLineAnchorGCD is the GCD over the selected indices.
--
--   SparseGCDAnchorCandidate keeps the point and finite whole-fibre branches and the same line coordinate and period-pair index. Its line condition is positive degree of the compressed GCD. sparseGCDAnchorLocus forgets the certificate and retains the exact underlying finite locus candidate. Cardinality bounds, exact equality with the full GCD, and frontier equivalence are proved separately.
-- source:
--   Derived sparse-GCD criterion for the A.1 frontier https://prove2.me/theorems/aa2fcba7-944a-414e-b9df-82c4f489201c. Starting from a nonzero polynomial p_i, retain another polynomial only when it lowers the GCD degree. This gives a GCD-preserving subfamily J with |J|+deg(G)<=deg(p_i)+1. For the canonical line slices deg(p_i)<=n, hence |J|<=n+1-deg(G), and at most n for positive-degree G. The complete proof also establishes minimum cardinality and exact candidate equivalence. Primary pinned sources: Finset.gcd_insert and Finset.gcd_dvd, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/GCDMonoid/Finset.lean; Polynomial.associated_of_dvd_of_natDegree_le, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Div.lean; Finset.exists_min_image, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Max.lean. This is a derived supporting theorem. Mission context: the elementary line case in Appendix A of Senthil Kumar K (2026), https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. The old family has m+n+1 slices. The subset depends on the polynomials; neither the maximum sample index m+n nor the integer-search bound changes. No efficient algorithm to find the subset or global geometric cost estimate is proved.

import Definitions.Def_WeierstrassEllipticZeta_LineAnchorGCD
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

noncomputable section
open scoped Classical

namespace TranscendenceTheory

/-- A smallest-cardinality subfamily preserving the normalized polynomial GCD.
This is a finite algebraic certificate, with no complexity claim for finding it. -/
def polynomialGCDCore {ι K : Type*} [Field K]
    (f : ι → Polynomial K) (s : Finset ι) : Finset ι :=
  Classical.choose (Finset.exists_min_image
    (s.powerset.filter (fun t => t.gcd f = s.gcd f)) Finset.card
    ⟨s, by simp⟩)

end TranscendenceTheory

namespace WeierstrassEllipticZeta

/-- Compress the canonical slice family. The existing zero-obstruction branch
is represented by the empty family, whose GCD is zero. -/
def lineAnchorGCDCore (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (b α : ℂ) : Finset ℕ :=
  if anchorObstruction S Q m b α = 0 then ∅ else
    TranscendenceTheory.polynomialGCDCore
      (fun j : ℕ => anchorSlice S Q b α j) (Finset.range (m + n + 1))

/-- The GCD evaluated on the selected subfamily. -/
def sparseLineAnchorGCD (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (b α : ℂ) : Polynomial ℂ :=
  (lineAnchorGCDCore S Q m n b α).gcd (fun j : ℕ => anchorSlice S Q b α j)

/-- The same locus choices, using the compressed GCD in the line condition. -/
abbrev SparseGCDAnchorCandidate (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) :=
  Unit ⊕ (↥Z ⊕ ((p : ↥(periodPairCandidates Λ X)) ×
    {b : K // 0 < (sparseLineAnchorGCD S Q m n b.val
      (periodPairSlope Λ η X p)).natDegree}))

def sparseGCDAnchorLocus (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) :
    SparseGCDAnchorCandidate Λ η X S Q m n K Z → FiniteLocusCandidate Λ X
  | .inl _ => .inl ()
  | .inr (.inl _) => .inr (.inl ())
  | .inr (.inr p) => .inr (.inr p.1)

end WeierstrassEllipticZeta


