-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_GradedModules
-- name    : DetSupportRank_DeterminantSupport_GradedModules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:24.176397+00:00
-- url     : https://prove2.me/theorems/0beb42f5-5a7e-42e9-aba3-43e7270862ef
-- title:
--   Graded modules and shifted free-module pieces
-- statement:
--   A graded module consists of an actual module $M$ over $S=F[x_v]$ and subspaces $M_u$ satisfying
--   $$M=\bigoplus_{u\in\mathbb Z^d}M_u,\qquad S_vM_w\subseteq M_{v+w}.$$
--   The direct sum is expressed by finite existence and uniqueness of homogeneous decompositions. A shifted free module with basis degrees $s_i$ has degree-$u$ piece spanned by the monomial basis vectors $x^ee_i$ with $\deg(x^e)+s_i=u$. Quotient pieces are the actual images of these subspaces, and submodule pieces are intersections.
--
--   The data record has no fields asserting resolution existence, K-polynomial identities, annihilation, or exactness after specialization. Valid grading and finite generation are imposed exactly where the source needs them.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §5.3 and §5.6, pp.18–23, p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_DegreeRelations

noncomputable section
open scoped BigOperators
universe uDSGradedModules

namespace DetSupportRank.DeterminantSupport

/-- A module with specified candidate homogeneous pieces. Validity is the direct-sum predicate below,
not a field containing any result about resolutions, K-polynomials or specialization. -/
structure GradedModuleData (K : Type uDSGradedModules) [Field K] (V D : Type) where
  Carrier : Type uDSGradedModules
  [addGroup : AddCommGroup Carrier]
  [scalar : Module (MvPolynomial V K) Carrier]
  [fieldScalar : Module K Carrier]
  [tower : IsScalarTower K (MvPolynomial V K) Carrier]
  piece : (D → ℤ) → Submodule K Carrier

attribute [instance] GradedModuleData.addGroup GradedModuleData.scalar
  GradedModuleData.fieldScalar GradedModuleData.tower

/-- Internal direct sum: existence of finite homogeneous decompositions and uniqueness. -/
def IsDirectGrading {K : Type uDSGradedModules} [Field K] {D : Type} {M : Type uDSGradedModules}
    [AddCommGroup M] [Module K M] (P : (D → ℤ) → Submodule K M) : Prop :=
  (∀ x : M, ∃ s : Finset (D → ℤ), ∃ v : (D → ℤ) → M,
    (∀ u ∈ s, v u ∈ P u) ∧ x = ∑ u ∈ s, v u) ∧
  (∀ (s : Finset (D → ℤ)) (v : (D → ℤ) → M),
    (∀ u ∈ s, v u ∈ P u) → (∑ u ∈ s, v u) = 0 → ∀ u ∈ s, v u = 0)

/-- The ordinary graded-module axioms for the given polynomial-ring weights. -/
def IsGraded {K : Type uDSGradedModules} [Field K] {V D : Type}
    (p : V → D → ℤ) (M : GradedModuleData K V D) : Prop :=
  IsDirectGrading M.piece ∧
  ∀ (v w : D → ℤ) (f : MvPolynomial V K), Homogeneous p v f →
    ∀ x ∈ M.piece w, f • x ∈ M.piece (v + w)

/-- Degree preservation for an actual module homomorphism. -/
def PreservesDegrees {K : Type uDSGradedModules} [Field K] {V D : Type}
    (M N : GradedModuleData K V D)
    (φ : M.Carrier →ₗ[MvPolynomial V K] N.Carrier) : Prop :=
  ∀ u, ∀ x ∈ M.piece u, φ x ∈ N.piece u

/-- Positive polynomial grading of §5.3, p.18. -/
def PositiveWeights {V D : Type} (p : V → D → ℤ) : Prop :=
  ∀ v, (∀ i, 0 ≤ p v i) ∧ p v ≠ 0

/-- The degree-u subspace in a shifted free module: span of its actual homogeneous monomials. -/
def freePiece {K : Type uDSGradedModules} [Field K] {V D : Type} {k : ℕ}
    (p : V → D → ℤ) (s : Fin k → D → ℤ) (u : D → ℤ) :
    Submodule K (Fin k → MvPolynomial V K) :=
  Submodule.span K {v | ∃ (i : Fin k) (e : V →₀ ℕ),
    monomialDegree p e + s i = u ∧
    v = Pi.single i (MvPolynomial.monomial e (1 : K))}

/-- Shifted free module, with no assumed positivity of its integer shifts. -/
def freeModuleData {K : Type uDSGradedModules} [Field K] {V D : Type} {k : ℕ}
    (p : V → D → ℤ) (s : Fin k → D → ℤ) : GradedModuleData K V D where
  Carrier := Fin k → MvPolynomial V K
  piece := freePiece p s

/-- Actual quotient of the shifted free module by its relations, with image pieces. -/
def quotientModuleData {K : Type uDSGradedModules} [Field K] {V D : Type} {k : ℕ}
    (p : V → D → ℤ) (s : Fin k → D → ℤ)
    (N : Submodule (MvPolynomial V K) (Fin k → MvPolynomial V K)) :
    GradedModuleData K V D where
  Carrier := (Fin k → MvPolynomial V K) ⧸ N
  piece u := (freePiece p s u).map (N.mkQ.restrictScalars K)

/-- Degree-u piece of a submodule, used in Proposition 5.18. -/
def submodulePiece {K : Type uDSGradedModules} [Field K] {V D : Type} {k : ℕ}
    (p : V → D → ℤ) (s : Fin k → D → ℤ)
    (N : Submodule (MvPolynomial V K) (Fin k → MvPolynomial V K))
    (u : D → ℤ) : Submodule K (Fin k → MvPolynomial V K) :=
  (N.restrictScalars K) ⊓ freePiece p s u

end DetSupportRank.DeterminantSupport


