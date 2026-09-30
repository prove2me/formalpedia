-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_FiniteAnchorCandidates
-- name    : WeierstrassEllipticZeta_FiniteAnchorCandidates
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-22T06:55:49.550892+00:00
-- url     : https://prove2.me/theorems/5f339579-1a46-4564-98f7-12df3b406649
-- title:
--   Finite anchor candidates from bounded-degree intercept polynomials
-- statement:
--   Write
--   $$F_Q(t,b,u)=Q(1,t,S_0(b),S_1(b),S_2(b),
--   S_3(b)+uS_0(b),S_4(b)+uS_2(b)).$$
--   For fixed $b,\alpha,t$, the intercept slice is the univariate polynomial
--   $F_Q(t,b,\alpha t+\beta)$ in $\beta$.
--
--   The obstruction polynomial is the first nonzero slice with integer
--   $t\in\{0,\ldots,m\}$, or zero if all these slices are zero. The line-anchor
--   root set consists of its distinct roots which also pass the canonical finite
--   line tests at anchor $(0,b,\beta)$.
--
--   At each fixed $b$, the finite anchor candidate type consists of:
--
--   - the origin point;
--   - the whole fibre at anchor $(0,b,0)$, included only when its finite tests pass;
--   - a period pair $(x,y)$ together with a root from the line-anchor root set for
--     slope $\eta(x-y)/(x-y)$.
--
--   The definitions provide projections to the previous finite locus candidate
--   and to its normalized anchor. The origin's vanishing is a hypothesis of the
--   supporting complete theorem, and follows from the analytic assumptions when
--   the definitions are used in A.1. No vanishing assumption is hidden in the
--   unconditional origin candidate.
--
--   These are mathematical finite sets using classical decisions about complex
--   coefficients and period membership. They do not provide numerical root
--   isolation or select the elliptic coordinate $b$.
-- source:
--   Derived finite-anchor reduction for the A.1 frontier https://prove2.me/theorems/2e690c3c-a614-4436-9c1d-2fcd2e9fae42. For a fixed elliptic coordinate b and slope alpha, form the univariate intercept slices F(j,b,alpha*j+beta), j=0,...,m. Each has degree at most n. The first nonzero slice has at most n roots. If every slice is zero, degree-m interpolation in the additive coordinate proves whole-fibre vanishing. The finite-anchor theorem and the frontier converse are derived here; they are not a theorem quoted from the mission paper. Primary root-counting reference: pinned Mathlib, Polynomial.card_roots' and Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A, Proposition A.1 case (4), surrounding (A.16), https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. At each b there are at most 2+n*|X|*(|X|-1) tested candidates. The origin point, normalized fibre anchor, and line roots remove free additive and vertical anchor coordinates. The elliptic coordinate b and uniform geometric cost estimate remain Open. The constant and degree parameter are preserved, while class count can decrease. No integer-search bound improvement or numerical root-finding algorithm is claimed.

import Definitions.Def_WeierstrassEllipticZeta_FiniteLocusCandidates
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fintype.Sigma

noncomputable section
open scoped Classical
namespace WeierstrassEllipticZeta

/-- The polynomial in the intercept at one fixed additive coordinate. -/
def anchorSlice (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (b α t : ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![1, Polynomial.C t, Polynomial.C (S 0 b), Polynomial.C (S 1 b),
      Polynomial.C (S 2 b),
      Polynomial.C (S 3 b) + (Polynomial.C (α * t) + Polynomial.X) * Polynomial.C (S 0 b),
      Polynomial.C (S 4 b) + (Polynomial.C (α * t) + Polynomial.X) * Polynomial.C (S 2 b)] Q

/-- The first nonzero integer slice, or zero when all m+1 slices vanish. -/
def anchorObstruction (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m : ℕ) (b α : ℂ) : Polynomial ℂ :=
  if h : ∃ j : ℕ, j ≤ m ∧ anchorSlice S Q b α j ≠ 0 then
    anchorSlice S Q b α (Nat.find h)
  else 0

/-- Polynomial roots which also pass all the line's finite vanishing tests. -/
def lineAnchorRoots (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (b α : ℂ) : Finset ℂ :=
  (anchorObstruction S Q m b α).roots.toFinset.filter (fun β =>
    ∀ w ∈ elementaryLocusSamples (.line α) ![0, b, β] m n,
      MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
        S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0)

/-- A whole-fibre candidate is present exactly when its finite tests pass. -/
def fibreAnchorChoices (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (b : ℂ) : Finset Unit :=
  ({()} : Finset Unit).filter (fun _ =>
    ∀ w ∈ elementaryLocusSamples .fibre ![0, b, 0] m n,
      MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
        S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0)

def periodPairSlope (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (p : ↥(periodPairCandidates Λ X)) : ℂ :=
  η (candidatePeriod Λ X p) / (candidatePeriod Λ X p : ℂ)

/-- At a fixed elliptic coordinate, the origin point, a tested fibre, or a
period-pair line with an intercept from the finite root set. -/
abbrev FiniteAnchorCandidate (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (b : ℂ) :=
  Unit ⊕ (↥(fibreAnchorChoices S Q m n b) ⊕
    ((p : ↥(periodPairCandidates Λ X)) ×
      ↥(lineAnchorRoots S Q m n b (periodPairSlope Λ η X p))))

def anchorCandidateLocus (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (b : ℂ) :
    FiniteAnchorCandidate Λ η X S Q m n b → FiniteLocusCandidate Λ X
  | .inl _ => .inl ()
  | .inr (.inl _) => .inr (.inl ())
  | .inr (.inr p) => .inr (.inr p.1)

def anchorCandidatePoint (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (b : ℂ) :
    FiniteAnchorCandidate Λ η X S Q m n b → (Fin 3 → ℂ)
  | .inl _ => 0
  | .inr (.inl _) => ![0, b, 0]
  | .inr (.inr p) => ![0, b, p.2.val]

end WeierstrassEllipticZeta


