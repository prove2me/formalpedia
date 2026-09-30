-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_OptimalAnchorWeight
-- name    : WeierstrassEllipticZeta_OptimalAnchorWeight
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-22T18:41:55.868651+00:00
-- url     : https://prove2.me/theorems/e6319d6e-6d31-4e4d-a288-13805a093d5f
-- title:
--   Candidate weights, their attained minimum and an optimal anchor
-- statement:
--   For each existing finite locus candidate, candidateClassCount is the number of classes represented by X modulo its elementary period kernel. candidateWeight assigns this class count k to a point and (m+1)*k to a line or whole fibre. This clears the two possible additive-degree factors in the existing cost estimate. sparseAnchorWeight evaluates this weight on a sparse-GCD anchor's underlying locus candidate.
--
--   minimumAnchorWeight is the least attained natural-number weight over all sparse-GCD anchors. The point branch always exists, so the defining natural-number minimum exists even if there are no fibre or line candidates. optimalSparseAnchor chooses a witness attaining this minimum. The choice depends on the locus data and degrees but not on a chart, chart point, local cost E, vanishing-order parameter U or constant C.
--
--   These are classical definitions: the feasibility predicate still includes the original coordinate and sparse-GCD conditions. No effective procedure for locating a coordinate, evaluating the minimum, or enumerating all anchors is built into the definitions. Attainment, optimality, size bounds, the nonpoint cutoff and equivalence of cost inequalities are proved in the companion theorem.
-- source:
--   Derived optimum-weight criterion for the A.1 frontier https://prove2.me/theorems/7e7bb591-b0c3-4c9f-a487-565853b9f422. A point has weight |X|; a nonpoint with k quotient classes has weight (m+1)*k. The least attained natural-number weight W exists, is at most |X|, and is positive for nonempty X. The same minimizing anchor works for all natural local costs E and real C, and existence of an old anchor budget is equivalent to W*E<=C*(m+1)*n^2. Every minimizing zero-additive-degree candidate has k<=floor(|X|/(m+1)). Primary pinned sources: Nat.find_spec and Nat.find_min', https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Find.lean; finite image cardinality, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Card.lean; quotient equality, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Quotient/Basic.lean. This is a derived optimization lemma, not the uniform geometric bound. Mission context: Appendix A of Senthil Kumar K (2026), https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. Coordinate feasibility remains classical. The same C, chart point and local cost are preserved; individual anchor coordinates, degrees and class counts may change. The integer-search and existing slice-count bounds are unchanged.

import Definitions.Def_WeierstrassEllipticZeta_SparseLineAnchorGCD
import Mathlib.Data.Nat.Find

noncomputable section
open scoped Classical
namespace WeierstrassEllipticZeta

/-- Number of classes represented by the finite input for a locus candidate. -/
def candidateClassCount (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (k : FiniteLocusCandidate Λ X) : ℕ :=
  (X.image (elementaryPeriodKernel Λ η (candidateLocusShape Λ η X k)).mkQ).card

/-- Clear the two possible degree denominators: weight k for a point,
and weight (m+1)*k for a line or whole fibre. -/
def candidateWeight (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (m : ℕ) (k : FiniteLocusCandidate Λ X) : ℕ :=
  match k with
  | .inl _ => candidateClassCount Λ η X k
  | .inr _ => (m + 1) * candidateClassCount Λ η X k

def sparseAnchorWeight (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ)
    (a : SparseGCDAnchorCandidate Λ η X S Q m n K Z) : ℕ :=
  candidateWeight Λ η X m (sparseGCDAnchorLocus Λ η X S Q m n K Z a)

/-- The least attained integer weight. The point branch guarantees existence.
This definition uses classical feasibility, not an effective coordinate search. -/
def minimumAnchorWeight (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) : ℕ :=
  Nat.find (show ∃ w : ℕ, ∃ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
      sparseAnchorWeight Λ η X S Q m n K Z a = w from
    ⟨sparseAnchorWeight Λ η X S Q m n K Z (.inl ()), .inl (), rfl⟩)

/-- A single minimizer, independent of chart, chart point, local cost and U. -/
def optimalSparseAnchor (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) :
    SparseGCDAnchorCandidate Λ η X S Q m n K Z :=
  Classical.choose (show ∃ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
      sparseAnchorWeight Λ η X S Q m n K Z a =
        minimumAnchorWeight Λ η X S Q m n K Z from
    Nat.find_spec (show ∃ w : ℕ, ∃ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
        sparseAnchorWeight Λ η X S Q m n K Z a = w from
      ⟨sparseAnchorWeight Λ η X S Q m n K Z (.inl ()), .inl (), rfl⟩))

end WeierstrassEllipticZeta


