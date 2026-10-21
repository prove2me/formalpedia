-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28
-- name    : QAlgorithms_Papers_Independent_Renew46_P28
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T02:54:34.368259+00:00
-- url     : https://prove2.me/theorems/b6cf6d12-05f2-4785-b1be-ac92eae4bf11
-- title:
--   Definitions for Lie groups over non-discrete topological fields
-- statement:
--   The objects the formalized statements of *Lie groups over non-discrete topological fields* (arXiv:math/0408008) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `differenceDomain`: Definition 1.4, PDF p.13: the first extended difference domain, with ambient product topology. Subtypes below always have their induced topologies.
--   - `puncturedDifferenceDomain`: Assertion 1.8, PDF p.14: the part of the first quotient domain with nonzero scalar parameter.
--   - `differenceQuotient`: Definition 1.5, PDF p.14: the actual difference quotient; zero parameters are excluded by the domain, not assigned a default value.
--   - `extendsDifferenceQuotient`: Equation (3), PDF p.14: a proposed first extended quotient agrees with all nonzero-parameter quotients. No continuity or differentiability is assumed here.
--   - `bgnFinite`: Definition 1.5 and its equivalent recursion 1.7, PDF p.14: finite-order source calculus. Each stage demands continuity and an actual continuous extended quotient, whose remaining regularity is recursively tested on the new open domain. The source and scalar universes are arranged to permit the ambient product to grow.
--   - `bgnCr`: Definition 1.5, PDF p.14: regularity in N_0 union {infinity}. Infinity requires every finite order. The lower orders are written explicitly; there are no arbitrary derivatives or regularity oracles in this predicate.
--   - `continuousInverseAlgebra`: Definition 2.1, PDF p.17: a Hausdorff associative unital topological K-algebra whose units are open and whose inverse map is continuous in the subspace topology. Ring.inverse is evaluated only on units.
--   - `canonicalFiniteVectorTopology`: Section 2.5, PDF p.18: the product topology in coordinates of a finite basis. This is transported to the actual space, without a norm assumption.
--   - `tensorCoordinateMap`: Proposition 2.7, PDF p.18: the explicit tensor coordinate map for a chosen basis of the finite-dimensional first tensor factor.
--   - `finiteTensorAlgebraTopology`: Proposition 2.7, PDF p.18: transport the product topology on A^n by its bijective tensor coordinate map. Module.Basis independence is a theorem conclusion.
--   - `locallyFiniteAlgebra`: Section 2.9, PDF p.20: every finite set is contained in a finite-dimensional unital subalgebra. Countable dimension is a separate hypothesis.
--   - `finiteTopology`: Section 2.10, PDF p.20: the final topology for inclusions of every finite-dimensional vector subspace, each with its canonical topology.
--   - `ProjectiveSystem`: Lemma 1.17, PDF p.16 (system conventions as in cited [3], Lemma 10.3): a projective system consists of continuous linear bonding maps on a directed set.
--   - `projectiveLimit`: The actual inverse limit: compatible tuples in the product, with its induced topology. This is a constructed subspace, not a free range constrained by an assumed regularity-testing property. Source: Lemma 1.17, PDF p.16.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, https://arxiv.org/abs/math/0408008v1

import Mathlib

/-!
Statements from H. Glöckner, arXiv:math/0408008v1.
The paper-local calculus uses continuous extended difference quotients over arbitrary
Hausdorff nondiscrete topological fields, without normed-space assumptions.
Compilation is pending the batch mechanical handoff.
-/

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set
open scoped TensorProduct

universe u v w

/-- Definition 1.4, PDF p.13: the first extended difference domain, with ambient
product topology. Subtypes below always have their induced topologies. -/
def differenceDomain (K : Type u) [Field K] {E : Type v}
    [AddCommGroup E] [Module K E] (U : Set E) : Set (E × E × K) :=
  {z | z.1 ∈ U ∧ z.1 + z.2.2 • z.2.1 ∈ U}

/-- Assertion 1.8, PDF p.14: the part of the first quotient domain with nonzero
scalar parameter. -/
def puncturedDifferenceDomain (K : Type u) [Field K] {E : Type v}
    [AddCommGroup E] [Module K E] (U : Set E) : Set (E × E × K) :=
  {z | z ∈ differenceDomain K U ∧ z.2.2 ≠ 0}

/-- Definition 1.5, PDF p.14: the actual difference quotient; zero parameters
are excluded by the domain, not assigned a default value. -/
def differenceQuotient (K : Type u) [Field K] {E : Type v}
    [AddCommGroup E] [Module K E] {F : Type w}
    [AddCommGroup F] [Module K F] (U : Set E) (f : U → F)
    (z : puncturedDifferenceDomain K U) : F :=
  z.val.2.2⁻¹ •
    (f ⟨z.val.1 + z.val.2.2 • z.val.2.1, z.property.1.2⟩ -
      f ⟨z.val.1, z.property.1.1⟩)

/-- Equation (3), PDF p.14: a proposed first extended quotient agrees with
all nonzero-parameter quotients. No continuity or differentiability is assumed here. -/
def extendsDifferenceQuotient (K : Type u) [Field K] {E : Type v}
    [AddCommGroup E] [Module K E] {F : Type w}
    [AddCommGroup F] [Module K F] (U : Set E) (f : U → F)
    (g : differenceDomain K U → F) : Prop :=
  ∀ z : puncturedDifferenceDomain K U,
    g ⟨z.val, z.property.1⟩ = differenceQuotient K U f z

/-- Definition 1.5 and its equivalent recursion 1.7, PDF p.14: finite-order
source calculus. Each stage demands continuity and an actual continuous extended
quotient, whose remaining regularity is recursively tested on the new open domain.
The source and scalar universes are arranged to permit the ambient product to grow. -/
def bgnFinite (K : Type u) [Field K] [TopologicalSpace K]
    (F : Type w) [AddCommGroup F] [Module K F] [TopologicalSpace F]
    (n : ℕ) {E : Type (max u v)} [AddCommGroup E] [Module K E]
    [TopologicalSpace E] (U : Set E) (f : U → F) : Prop :=
  match n with
  | 0 => Continuous f
  | n + 1 => Continuous f ∧
      ∃ g : differenceDomain K U → F,
        Continuous g ∧ extendsDifferenceQuotient K U f g ∧
          bgnFinite K F n (differenceDomain K U) g
termination_by n

/-- Definition 1.5, PDF p.14: regularity in N_0 union {infinity}.
Infinity requires every finite order. The lower orders are written explicitly;
there are no arbitrary derivatives or regularity oracles in this predicate. -/
def bgnCr (K : Type u) [Field K] [TopologicalSpace K]
    (F : Type w) [AddCommGroup F] [Module K F] [TopologicalSpace F]
    (k : WithTop ℕ) {E : Type (max u v)} [AddCommGroup E] [Module K E]
    [TopologicalSpace E] (U : Set E) (f : U → F) : Prop :=
  ∀ n : ℕ, (n : WithTop ℕ) ≤ k → bgnFinite K F n U f

/-- Sanity check for Definition 1.4: the zero-parameter slice is exactly U × E. -/
example (K : Type u) [Field K] (E : Type v) [AddCommGroup E]
    [Module K E] (U : Set E) (x y : E) :
    (x, y, (0 : K)) ∈ differenceDomain K U ↔ x ∈ U := by
  simp [differenceDomain]

/-- Sanity check: finite order zero is continuity, including on the empty domain. -/
example (K : Type u) [Field K] [TopologicalSpace K]
    (E : Type (max u v)) [AddCommGroup E] [Module K E] [TopologicalSpace E]
    (F : Type w) [AddCommGroup F] [Module K F] [TopologicalSpace F]
    (U : Set E) (f : U → F) : bgnFinite K F 0 U f ↔ Continuous f := by
  simp [bgnFinite]

/-- Sanity check for the quotient sign and scalar: a constant map has zero quotient. -/
example (K : Type u) [Field K] (E : Type v) [AddCommGroup E]
    [Module K E] (F : Type w) [AddCommGroup F] [Module K F]
    (U : Set E) (c : F) (z : puncturedDifferenceDomain K U) :
    differenceQuotient K U (fun _ => c) z = 0 := by
  simp [differenceQuotient]

/-- Definition 2.1, PDF p.17: a Hausdorff associative unital topological
K-algebra whose units are open and whose inverse map is continuous in the
subspace topology. Ring.inverse is evaluated only on units. -/
def continuousInverseAlgebra (K : Type u) [Field K] [TopologicalSpace K]
    (A : Type v) [Ring A] [Algebra K A] [TopologicalSpace A] : Prop :=
  T2Space A ∧ IsTopologicalRing A ∧ ContinuousSMul K A ∧
    IsOpen {a : A | IsUnit a} ∧
    Continuous (fun a : {a : A // IsUnit a} => Ring.inverse a.val)

/-- Section 2.5, PDF p.18: the product topology in coordinates of a finite
basis. This is transported to the actual space, without a norm assumption. -/
noncomputable def canonicalFiniteVectorTopology
    (K : Type u) [Field K] [TopologicalSpace K]
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    TopologicalSpace V :=
  TopologicalSpace.induced (Module.finBasis K V).equivFun inferInstance

/-- Proposition 2.7, PDF p.18: the explicit tensor coordinate map for a
chosen basis of the finite-dimensional first tensor factor. -/
noncomputable def tensorCoordinateMap (K : Type u) [Field K]
    {F : Type v} [AddCommGroup F] [Module K F]
    {A : Type w} [AddCommGroup A] [Module K A]
    {n : ℕ} (b : Module.Basis (Fin n) K F) (a : Fin n → A) : F ⊗[K] A :=
  ∑ i, TensorProduct.tmul K (b i) (a i)

/-- Proposition 2.7, PDF p.18: transport the product topology on A^n by
its bijective tensor coordinate map. Module.Basis independence is a theorem conclusion. -/
noncomputable def finiteTensorAlgebraTopology (K : Type u) [Field K]
    {F : Type v} [AddCommGroup F] [Module K F]
    (A : Type w) [AddCommGroup A] [Module K A] [TopologicalSpace A]
    {n : ℕ} (b : Module.Basis (Fin n) K F) : TopologicalSpace (F ⊗[K] A) :=
  TopologicalSpace.coinduced (tensorCoordinateMap K b) inferInstance

/-- Section 2.9, PDF p.20: every finite set is contained in a finite-dimensional
unital subalgebra. Countable dimension is a separate hypothesis. -/
def locallyFiniteAlgebra (K : Type u) [Field K]
    (A : Type v) [Ring A] [Algebra K A] : Prop :=
  ∀ s : Finset A, ∃ B : Subalgebra K A,
    FiniteDimensional K B ∧ ∀ a ∈ s, a ∈ B

/-- Section 2.10, PDF p.20: the final topology for inclusions of every
finite-dimensional vector subspace, each with its canonical topology. -/
noncomputable def finiteTopology (K : Type u) [Field K] [TopologicalSpace K]
    (A : Type v) [AddCommGroup A] [Module K A] : TopologicalSpace A :=
  ⨆ S : {S : Submodule K A // FiniteDimensional K S},
    letI : FiniteDimensional K S.val := S.property
    TopologicalSpace.coinduced (fun a : S.val => (a : A))
      (canonicalFiniteVectorTopology K S.val)

/-- Sanity check: a tensor coordinate map sends the zero tuple to zero. -/
example (K : Type u) [Field K] (F : Type v) [AddCommGroup F]
    [Module K F] (A : Type w) [AddCommGroup A] [Module K A]
    {n : ℕ} (b : Module.Basis (Fin n) K F) :
    tensorCoordinateMap K b (0 : Fin n → A) = 0 := by
  simp [tensorCoordinateMap]

/-- Sanity check: the CIA predicate uses the two-sided inverse of a unit. -/
example (A : Type v) [Ring A] (a : {a : A // IsUnit a}) :
    a.val * Ring.inverse a.val = 1 ∧ Ring.inverse a.val * a.val = 1 := by
  exact ⟨Ring.mul_inverse_cancel a.val a.property,
    Ring.inverse_mul_cancel a.val a.property⟩

/-- Sanity check: the canonical topology on the zero-dimensional space is
its unique topology, also when the scalar field is not normable. -/
example (K : Type u) [Field K] [TopologicalSpace K] :
    canonicalFiniteVectorTopology K (Fin 0 → K) =
      (⊤ : TopologicalSpace (Fin 0 → K)) := by
  exact Subsingleton.elim _ _

/-- Sanity check: the finite topology on the zero-dimensional space is
likewise the unique topology. -/
example (K : Type u) [Field K] [TopologicalSpace K] :
    finiteTopology K (Fin 0 → K) = (⊤ : TopologicalSpace (Fin 0 → K)) := by
  exact Subsingleton.elim _ _

/-- Sanity check: every finite-dimensional algebra is locally finite; the
containing subalgebra may be the whole algebra and has the same identity. -/
example (K : Type u) [Field K] (A : Type v) [Ring A] [Algebra K A]
    [FiniteDimensional K A] : locallyFiniteAlgebra K A := by
  intro s
  refine ⟨⊤, inferInstance, ?_⟩
  intro a ha
  trivial

/-- Lemma 1.17, PDF p.16 (system conventions as in cited [3], Lemma 10.3):
a projective system consists of continuous linear bonding maps on a directed set. -/
structure ProjectiveSystem (K : Type u) [Field K] [TopologicalSpace K]
    {I : Type v} [Preorder I] (Fi : I → Type w)
    [∀ i, AddCommGroup (Fi i)] [∀ i, Module K (Fi i)]
    [∀ i, TopologicalSpace (Fi i)] where
  bonding : ∀ i j, i ≤ j → (Fi j →L[K] Fi i)
  identity : ∀ i x, bonding i i le_rfl x = x
  composition : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) x,
    bonding i j hij (bonding j k hjk x) = bonding i k (le_trans hij hjk) x

/-- The actual inverse limit: compatible tuples in the product, with its
induced topology. This is a constructed subspace, not a free range constrained
by an assumed regularity-testing property. Source: Lemma 1.17, PDF p.16. -/
def projectiveLimit (K : Type u) [Field K] [TopologicalSpace K]
    {I : Type v} [Preorder I] (Fi : I → Type w)
    [∀ i, AddCommGroup (Fi i)] [∀ i, Module K (Fi i)]
    [∀ i, TopologicalSpace (Fi i)] (S : ProjectiveSystem K Fi) :
    Submodule K (∀ i, Fi i) where
  carrier := {x | ∀ i j (h : i ≤ j), S.bonding i j h (x j) = x i}
  zero_mem' := by
    intro i j h
    exact map_zero (S.bonding i j h)
  add_mem' := by
    intro x y hx hy i j h
    change S.bonding i j h (x j + y j) = x i + y i
    rw [map_add, hx i j h, hy i j h]
  smul_mem' := by
    intro c x hx i j h
    change S.bonding i j h (c • x j) = c • x i
    rw [map_smul, hx i j h]

/-- Sanity check: the zero tuple satisfies every bonding equation. -/
example (K : Type u) [Field K] [TopologicalSpace K]
    {I : Type v} [Preorder I] (Fi : I → Type w)
    [∀ i, AddCommGroup (Fi i)] [∀ i, Module K (Fi i)]
    [∀ i, TopologicalSpace (Fi i)] (S : ProjectiveSystem K Fi)
    (i j : I) (h : i ≤ j) :
    S.bonding i j h ((0 : projectiveLimit K Fi S).val j) =
      (0 : projectiveLimit K Fi S).val i := by
  exact (0 : projectiveLimit K Fi S).property i j h

end QAlgorithms.Papers.Independent.Renew46.P28


