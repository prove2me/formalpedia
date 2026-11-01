-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P67
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P67
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:23:05.072702+00:00
-- url     : https://prove2.me/theorems/b4123912-6f51-4d1b-9c4d-da6ca6623b02
-- title:
--   Definitions for Central extensions of groups of sections
-- statement:
--   The objects the formalized statements of *Central extensions of groups of sections* (arXiv:0711.3437) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `universalRelations`: Definition B.1, PDF p. 41: the relations imposing symmetry and killing the natural infinitesimal adjoint action on the symmetric tensor square. Taking their linear span implements both successive quotients at once.
--   - `UniversalFormSpace`: Definition B.1, PDF p. 41: the universal coefficient space V(L). It is an algebraic quotient; no completion or closure is taken.
--   - `universalForm`: Definition B.1, PDF p. 41: κu(x,y) is the class of x tensor y. Modulo symmetry this also equals the class of (x tensor y + y tensor x)/2, so the source's symmetric-product normalization is preserved.
--   - `InvariantSymmetric`: Definition B.1, PDF p. 41, and the invariance convention on p. 8. Bilinearity is carried by the type of B; both remaining conditions are explicit.
--   - `universalMap`: Remark B.2(a), PDF p. 41: apply a Lie homomorphism to both tensor factors and descend to the actual universal quotient. The descent proof checks both families of defining relations, rather than assuming functoriality.
--   - `universalFormSpan`: Theorem B.6, PDF pp. 42–43: κu(U,W) means its linear span. A raw image of a bilinear map would not in general be a vector subspace.
--   - `leviIsotypicSubspace`: Theorem B.6, PDF pp. 40, 42–43: the isotypic subspace in the chosen Levi complement, embedded into L. The supplied Lie isomorphism is the source's chosen decomposition s = direct_sum_i S_i^(m_i).
--   - `automorphismTopology`: Remark B.3, PDF p. 41: the ordinary topology on the automorphism group of a finite-dimensional real Lie algebra. With the Hausdorff real vector-space topology on L, this is pointwise convergence, equivalently the usual matrix topology. No Lie topology is imposed on an unrelated group.
-- source:
--   Central extensions of groups of sections, arXiv:0711.3437v2, https://arxiv.org/abs/0711.3437v2

import Mathlib

/-!
Algebraic statements from Neeb–Wockel, arXiv:0711.3437v2, Appendix B.
The remaining full-paper nodes are explicitly deferred in the unit's HARD.md
and GAPS.json. All definitions below are local to this paper. The universal
form is presented by the simultaneous symmetry and infinitesimal-invariance
relations in the tensor square, the single-quotient presentation of
S²(k)/(k · S²(k)). No analytic period object is replaced by an abstract map.
Compilation and independent moderation are pending the batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P67

open scoped TensorProduct

universe u v w

/-- Remark B.2(d) and Theorem B.6, PDF pp. 41–43: finite products of
Lie algebras use the componentwise bracket. This local instance also covers
the empty product and the nested products for repeated simple factors. -/
local instance dependentLieRing {I : Type*} (A : I → Type*)
    [∀ i, LieRing (A i)] : LieRing ((i : I) → A i) where
  bracket x y i := ⁅x i, y i⁆
  add_lie x y z := funext fun i => LieRing.add_lie (x i) (y i) (z i)
  lie_add x y z := funext fun i => LieRing.lie_add (x i) (y i) (z i)
  lie_self x := funext fun i => LieRing.lie_self (x i)
  leibniz_lie x y z := funext fun i => LieRing.leibniz_lie (x i) (y i) (z i)

/-- Remark B.2(d) and Theorem B.6, PDF pp. 41–43: the componentwise
real module structure is compatible with the componentwise Lie bracket. -/
local instance dependentLieAlgebra {I : Type*} (A : I → Type*)
    [∀ i, LieRing (A i)] [∀ i, LieAlgebra ℝ (A i)] :
    LieAlgebra ℝ ((i : I) → A i) where
  lie_smul t x y := funext fun i => LieAlgebra.lie_smul t (x i) (y i)

/-- Sanity: the bracket on a product is exactly the bracket in each factor. -/
example {I : Type*} (A : I → Type*) [∀ i, LieRing (A i)]
    (x y : (i : I) → A i) (i : I) : ⁅x, y⁆ i = ⁅x i, y i⁆ := rfl

/-- Sanity: scalar compatibility is checked in each real Lie algebra factor. -/
example {I : Type*} (A : I → Type*)
    [∀ i, LieRing (A i)] [∀ i, LieAlgebra ℝ (A i)]
    (t : ℝ) (x y : (i : I) → A i) (i : I) :
    ⁅x, t • y⁆ i = t • ⁅x i, y i⁆ := LieAlgebra.lie_smul t (x i) (y i)

section UniversalForm

variable (L : Type u) [LieRing L] [LieAlgebra ℝ L]

/-- Definition B.1, PDF p. 41: the relations imposing symmetry and killing
the natural infinitesimal adjoint action on the symmetric tensor square.
Taking their linear span implements both successive quotients at once. -/
def universalRelations : Submodule ℝ (L ⊗[ℝ] L) :=
  Submodule.span ℝ {t |
    (∃ x y : L, t = x ⊗ₜ[ℝ] y - y ⊗ₜ[ℝ] x) ∨
    (∃ x y z : L, t = ⁅x, y⁆ ⊗ₜ[ℝ] z + y ⊗ₜ[ℝ] ⁅x, z⁆)}

/-- Sanity: the defining symmetry relation is present in the actual submodule. -/
example (x y : L) : x ⊗ₜ[ℝ] y - y ⊗ₜ[ℝ] x ∈ universalRelations L :=
  Submodule.subset_span (Or.inl ⟨x, y, rfl⟩)

/-- Sanity: the complete infinitesimal adjoint-action relation is killed. -/
example (x y z : L) :
    ⁅x, y⁆ ⊗ₜ[ℝ] z + y ⊗ₜ[ℝ] ⁅x, z⁆ ∈ universalRelations L :=
  Submodule.subset_span (Or.inr ⟨x, y, z, rfl⟩)

/-- Definition B.1, PDF p. 41: the universal coefficient space V(L).
It is an algebraic quotient; no completion or closure is taken. -/
abbrev UniversalFormSpace := (L ⊗[ℝ] L) ⧸ universalRelations L

/-- Definition B.1, PDF p. 41: κu(x,y) is the class of x tensor y.
Modulo symmetry this also equals the class of (x tensor y + y tensor x)/2,
so the source's symmetric-product normalization is preserved. -/
def universalForm : L →ₗ[ℝ] L →ₗ[ℝ] UniversalFormSpace L :=
  (TensorProduct.mk ℝ L L).compr₂ (universalRelations L).mkQ

/-- Sanity: the tensor-class prescription is literal, with no choice of a form. -/
example (x y : L) :
    universalForm L x y = (universalRelations L).mkQ (x ⊗ₜ[ℝ] y) := rfl

/-- Sanity: a zero input gives zero, including in the zero-dimensional algebra. -/
example (y : L) : universalForm L 0 y = 0 := by
  simp [universalForm]

/-- Definition B.1, PDF p. 41, and the invariance convention on p. 8.
Bilinearity is carried by the type of B; both remaining conditions are explicit. -/
def InvariantSymmetric {W : Type v} [AddCommGroup W] [Module ℝ W]
    (B : L →ₗ[ℝ] L →ₗ[ℝ] W) : Prop :=
  (∀ x y, B x y = B y x) ∧
    (∀ x y z, B ⁅x, y⁆ z = B x ⁅y, z⁆)

/-- Sanity: the zero bilinear form satisfies both conditions. -/
example {W : Type v} [AddCommGroup W] [Module ℝ W] :
    InvariantSymmetric L (0 : L →ₗ[ℝ] L →ₗ[ℝ] W) := by
  constructor <;> intros <;> rfl

end UniversalForm

section Functor

variable {L : Type u} {M : Type v}
variable [LieRing L] [LieAlgebra ℝ L] [LieRing M] [LieAlgebra ℝ M]

/-- Remark B.2(a), PDF p. 41: apply a Lie homomorphism to both tensor factors
and descend to the actual universal quotient. The descent proof checks both
families of defining relations, rather than assuming functoriality. -/
def universalMap (f : L →ₗ⁅ℝ⁆ M) :
    UniversalFormSpace L →ₗ[ℝ] UniversalFormSpace M :=
  (universalRelations L).mapQ (universalRelations M)
    (TensorProduct.map f.toLinearMap f.toLinearMap) (by
      apply Submodule.span_le.mpr
      intro t ht
      change (TensorProduct.map f.toLinearMap f.toLinearMap) t ∈ universalRelations M
      rcases ht with ⟨x, y, rfl⟩ | ⟨x, y, z, rfl⟩
      · simp only [map_sub, TensorProduct.map_tmul]
        exact Submodule.subset_span (Or.inl ⟨f x, f y, rfl⟩)
      · simp only [map_add, TensorProduct.map_tmul]
        change f ⁅x, y⁆ ⊗ₜ[ℝ] f z + f y ⊗ₜ[ℝ] f ⁅x, z⁆ ∈ universalRelations M
        rw [f.map_lie, f.map_lie]
        exact Submodule.subset_span (Or.inr ⟨f x, f y, f z, rfl⟩))

/-- Sanity: the induced map sends the source's specified generator to its image. -/
example (f : L →ₗ⁅ℝ⁆ M) (x y : L) :
    universalMap f (universalForm L x y) = universalForm M (f x) (f y) := rfl

end Functor

section LeviDecomposition

variable (L : Type u) [LieRing L] [LieAlgebra ℝ L]

/-- Theorem B.6, PDF pp. 42–43: κu(U,W) means its linear span.
A raw image of a bilinear map would not in general be a vector subspace. -/
def universalFormSpan (U W : Submodule ℝ L) : Submodule ℝ (UniversalFormSpace L) :=
  Submodule.span ℝ {v | ∃ x ∈ U, ∃ y ∈ W, v = universalForm L x y}

/-- Sanity: every specified generator lies in this span. -/
example (U W : Submodule ℝ L) (x y : L) (hx : x ∈ U) (hy : y ∈ W) :
    universalForm L x y ∈ universalFormSpan L U W :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

/-- Theorem B.6, PDF pp. 40, 42–43: the isotypic subspace in the chosen
Levi complement, embedded into L. The supplied Lie isomorphism is the
source's chosen decomposition s = direct_sum_i S_i^(m_i). -/
def leviIsotypicSubspace {r : ℕ} (s : LieSubalgebra ℝ L)
    (S : Fin r → Type v) [∀ i, LieRing (S i)] [∀ i, LieAlgebra ℝ (S i)]
    (m : Fin r → ℕ) (e : s ≃ₗ⁅ℝ⁆ ((i : Fin r) → Fin (m i) → S i))
    (i : Fin r) : Submodule ℝ L :=
  Submodule.span ℝ (Set.range (fun x : Fin (m i) → S i =>
    s.incl (e.symm (Pi.single i x))))

/-- Sanity: a vector in one isotypic factor is embedded through the chosen
Levi decomposition and the actual inclusion of s into L. -/
example {r : ℕ} (s : LieSubalgebra ℝ L)
    (S : Fin r → Type v) [∀ i, LieRing (S i)] [∀ i, LieAlgebra ℝ (S i)]
    (m : Fin r → ℕ) (e : s ≃ₗ⁅ℝ⁆ ((i : Fin r) → Fin (m i) → S i))
    (i : Fin r) (x : Fin (m i) → S i) :
    s.incl (e.symm (Pi.single i x)) ∈ leviIsotypicSubspace L s S m e i :=
  Submodule.subset_span ⟨x, rfl⟩

end LeviDecomposition

section NaturalActions

variable (L : Type u) [LieRing L] [LieAlgebra ℝ L]

/-- Remark B.3, PDF p. 41: the ordinary topology on the automorphism group
of a finite-dimensional real Lie algebra. With the Hausdorff real
vector-space topology on L, this is pointwise convergence, equivalently
the usual matrix topology. No Lie topology is imposed on an unrelated group. -/
def automorphismTopology [TopologicalSpace L] : TopologicalSpace (L ≃ₗ⁅ℝ⁆ L) :=
  TopologicalSpace.induced (fun a : L ≃ₗ⁅ℝ⁆ L => (fun x : L => a x)) inferInstance

/-- Sanity: the topology is defined using the actual automorphism evaluations. -/
example [TopologicalSpace L] : automorphismTopology L =
    TopologicalSpace.induced (fun a : L ≃ₗ⁅ℝ⁆ L => (fun x : L => a x))
      (inferInstance : TopologicalSpace (L → L)) := rfl

attribute [local instance] LieRing.ofAssociativeRing

end NaturalActions

section MatrixExample

attribute [local instance] LieRing.ofAssociativeRing

end MatrixExample

end QAlgorithms.Papers.Independent.Intakenext100.P67


