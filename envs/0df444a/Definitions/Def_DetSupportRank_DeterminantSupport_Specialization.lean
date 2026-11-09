-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_Specialization
-- name    : DetSupportRank_DeterminantSupport_Specialization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:59.342772+00:00
-- url     : https://prove2.me/theorems/45d76673-42bf-40bd-ac16-a2ba580702b8
-- title:
--   Specialization of modules and maps at an evaluation point
-- statement:
--   Evaluation at $c$ agrees with the grading when every homogeneous polynomial of nonzero degree vanishes at $c$. The specialized vector space is the genuine extension of scalars
--   $$M(c)=M/\operatorname{span}_F\{s m-s(c)m:s\in S,\ m\in M\}.$$
--   The induced specialization of an $S$-linear map is defined on this quotient. Candidate degree pieces are the images of $M_u$, hence their $F$-spans. For a finite-dimensional directly graded vector space, its K-polynomial is the finite Laurent sum $\sum_u\dim_F(M_u)t^u$; the auxiliary total extension is zero if the set of nonzero pieces is infinite.
--
--   No flatness or exactness is assumed. The finite-dimensional use is after specializing a finite free module, where agreement preserves its finite homogeneous basis.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Definitions 5.20 and 5.23, pp.23–24; Remark 5.11, p.19, p. 23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_KPolynomials

noncomputable section
open scoped BigOperators
universe uDSSpec

namespace DetSupportRank.DeterminantSupport

/-- Definition 5.20, for arbitrary integer gradings, including zero-degree variables. -/
def AgreesWithGrading {K : Type*} [Field K] {V D : Type}
    (p : V → D → ℤ) (c : V → K) : Prop :=
  ∀ w : D → ℤ, w ≠ 0 → ∀ f : MvPolynomial V K,
    Homogeneous p w f → MvPolynomial.eval c f = 0

/-- Relations of extension of scalars to K along evaluation at c.
The quotient is M ⊗[S] K, written as a K-vector-space quotient without chosen generators. -/
def evaluationRelations {K : Type uDSSpec} [Field K] {V D : Type}
    (M : GradedModuleData K V D) (c : V → K) : Submodule K M.Carrier :=
  Submodule.span K {v | ∃ (f : MvPolynomial V K) (x : M.Carrier),
    v = f • x - (MvPolynomial.eval c f) • x}

/-- The actual specialized vector space M(c), not a free variable constrained by conclusions. -/
abbrev specializedSpace {K : Type uDSSpec} [Field K] {V D : Type}
    (M : GradedModuleData K V D) (c : V → K) :=
  M.Carrier ⧸ evaluationRelations M c

/-- Specialization m ↦ m(c). -/
def specializationMap {K : Type uDSSpec} [Field K] {V D : Type}
    (M : GradedModuleData K V D) (c : V → K) : M.Carrier →ₗ[K] specializedSpace M c :=
  (evaluationRelations M c).mkQ

/-- The image of M_u; since specialization is K-linear this equals the stated K-span. -/
def specializedPiece {K : Type uDSSpec} [Field K] {V D : Type}
    (M : GradedModuleData K V D) (c : V → K) (u : D → ℤ) :
    Submodule K (specializedSpace M c) :=
  (M.piece u).map (specializationMap M c)

/-- The induced map on specialization. Its well-definedness uses only linearity. -/
def specializeLinearMap {K : Type uDSSpec} [Field K] {V D : Type}
    (M N : GradedModuleData K V D) (c : V → K)
    (φ : M.Carrier →ₗ[MvPolynomial V K] N.Carrier) :
    specializedSpace M c →ₗ[K] specializedSpace N c := by
  apply Submodule.mapQ _ _ (φ.restrictScalars K)
  apply Submodule.span_le.mpr
  rintro x ⟨f, y, rfl⟩
  change φ (f • y - (MvPolynomial.eval c f) • y) ∈ evaluationRelations N c
  have hs : φ ((MvPolynomial.eval c f) • y) = (MvPolynomial.eval c f) • φ y :=
    (φ.restrictScalars K).map_smul _ _
  rw [map_sub, map_smul, hs]
  exact Submodule.subset_span ⟨f, φ y, rfl⟩

/-- K of a finite-dimensional graded vector space: its genuine finite Laurent Hilbert series.
The sum uses exactly the degrees with nonzero pieces. It is not used on an infinite support. -/
def vectorKPolynomial {K : Type uDSSpec} [Field K] {D : Type} {M : Type uDSSpec}
    [AddCommGroup M] [Module K M] (P : (D → ℤ) → Submodule K M) :
    AddMonoidAlgebra ℤ (D → ℤ) := by
  classical
  exact if h : Set.Finite {u | P u ≠ ⊥} then
    ∑ u ∈ h.toFinset, AddMonoidAlgebra.single u (Module.finrank K (P u) : ℤ)
  else 0

/-- Multiplication annihilates the actual module. -/
def Annihilates {K : Type uDSSpec} [Field K] {V D : Type}
    (f : MvPolynomial V K) (M : GradedModuleData K V D) : Prop :=
  ∀ x : M.Carrier, f • x = 0

end DetSupportRank.DeterminantSupport


