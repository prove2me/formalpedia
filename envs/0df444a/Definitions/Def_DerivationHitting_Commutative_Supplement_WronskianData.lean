-- Prove2me | Definitions.Def_DerivationHitting_Commutative_Supplement_WronskianData
-- name    : DerivationHitting_Commutative_Supplement_WronskianData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:55:41.350596+00:00
-- url     : https://prove2.me/theorems/f9d93ecd-745e-412c-8398-e02bc2427f32
-- title:
--   Degree-compatible chosen bases and the commutative D-Wronskian matrix
-- statement:
--   Let F be a field, let f be a commutative polynomial in n variables, and let g₁,…,gᵣ be a family. A degree-compatible basis is linearly independent, spans the published ordinary derivative space of f, is ordered by total degree, and spans each degree-filtration piece using its members of degree at most that level. This makes the basis choice in §3 explicit even when degrees repeat.
--
--   For arbitrary rational kernels bᵢ(t), reuse the published operator D=∂ₜ+Σᵢbᵢ(t)∂ₓᵢ and the embedding of F[x] into F(t)[x]. Define the matrix, rather than just its determinant, by
--
--   $$W_D(m,j)=D^m g_j,\qquad 0\le m<r.$$
--
--   There are no normalizations of nonzero scalar polynomials and no nonvanishing or factorization certificates in this definition. The derivative space, rational differentiation and coefficient embeddings are imported from their published base bundles.
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026). Canonical submission artifact, not proceedings publication; no arXiv pin. Printed page = PDF page throughout 1–29. pp.12–14, §3 setup and Theorem 3.2; degree-filtration reading documented in SUPPLEMENT.md.

import Definitions.Def_DerivationHitting_Commutative_DifferentialData

namespace DerivationHitting.Commutative.Supplement
noncomputable section

/-- The chosen basis spans each degree-filtration piece, and is ordered by degree.
Unlike mere degree sorting, this implies the earlier-index derivative relations. -/
def DegreeCompatibleBasis {F : Type*} [Field F] {n r : ℕ}
    (f : MvPolynomial (Fin n) F) (g : Fin r → MvPolynomial (Fin n) F) : Prop :=
  LinearIndependent F g ∧
  Submodule.span F (Set.range g) = partialSpace f ∧
  (∀ i j, i ≤ j → (g i).totalDegree ≤ (g j).totalDegree) ∧
  ∀ (d : ℕ) (p : MvPolynomial (Fin n) F),
    (p ∈ partialSpace f ∧ p.totalDegree ≤ d) ↔
      p ∈ Submodule.span F {q | ∃ j, g j = q ∧ (g j).totalDegree ≤ d}

/-- The matrix itself, rather than the published determinant. -/
def derivationWronskianMatrix {F : Type*} [Field F] {n r : ℕ}
    (b : Fin n → RatFunc F) (g : Fin r → MvPolynomial (Fin n) F) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin n) (RatFunc F)) :=
  fun m j => (linearDerivation b)^[m.val] (rationalPolynomial (g j))

end
end DerivationHitting.Commutative.Supplement


