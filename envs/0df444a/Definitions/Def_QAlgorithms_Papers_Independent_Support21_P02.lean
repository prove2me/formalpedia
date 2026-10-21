-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P02
-- name    : QAlgorithms_Papers_Independent_Support21_P02
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T03:26:47.249895+00:00
-- url     : https://prove2.me/theorems/6efefac7-1df2-478e-a303-90e956625ff0
-- title:
--   Definitions for A Cocycle Model for Topological and Lie Group Cohomology
-- statement:
--   The objects the formalized statements of *A Cocycle Model for Topological and Lie Group Cohomology* (arXiv:1110.3304) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SequenceClass`: Definition VI.1, PDF p. 24: a category with distinguished composable pairs. There are no exact-category axioms on the source category.
--   - `DistinguishedSequence`: Definition VI.1, PDF p. 24: one distinguished sequence A -> B -> D.
--   - `SequenceMap`: Definition VI.1, PDF pp. 24--25: the two commuting squares of a morphism between distinguished sequences.
--   - `ExactPair`: Definition VI.1, PDF pp. 24--25: exactness of two abelian-group homomorphisms at their common object, with no assertion at either end.
--   - `DeltaFunctor`: Definition VI.1, PDF pp. 24--25: a cohomological delta-functor. The three exactness clauses encode the long exact sequence, including H^0(B) and H^0(D); exactness at H^0(A) is deliberately not required (footnote 18). Connecting maps are natural for every sequence map.
--   - `DegreeFamily`: Definition VI.1, PDF p. 25: a degreewise natural family, before any compatibility with connecting maps is imposed.
--   - `CommutesConnecting`: Definition VI.1, PDF p. 25, diagram (16).
--   - `DeltaMorphism`: Definition VI.1, PDF p. 25: a morphism of delta-functors.
--   - `DeltaEquivalence`: Definition VI.1, PDF p. 25: mutually inverse delta-functor morphisms, including their inverse identities as natural transformations.
--   - `FunctorialResolution`: Theorem VI.2, PDF p. 25: the natural distinguished sequences used for dimension shifting. These are the theorem's supplied I,U,iota,zeta, not resolutions assumed to have any comparison maps.
--   - `FunctorialResolution.sequence`: Theorem VI.2, PDF p. 25: the distinguished sequence at A.
--   - `CompatibleQuotients`: Theorem VI.2(2), PDF p. 25: existence of Q_f, beta_f, gamma_f with the distinguished lower sequence and both diagrams (17). The unrecorded leftmost square in the first diagram is exactly naturality of iota, which is already a field of the natural transformation R.iota.
--   - `FiniteFamily`: Theorem VI.2(1), PDF p. 25: a family with exactly degrees 0,...,m. There are no components in degrees greater than m.
--   - `FiniteResolutionExtension`: Theorem VI.2(1), PDF p. 25: the resolution connecting squares in precisely the finite range n < m.
--   - `FiniteConnectingCompatibility`: Theorem VI.2(2), PDF p. 25: all distinguished-sequence connecting squares, restricted to the range for which both components exist.
--   - `ResolutionExtension`: Theorem VI.2, PDF pp. 25--26: the all-degree resolution squares.
-- source:
--   A Cocycle Model for Topological and Lie Group Cohomology, arXiv:1110.3304v3, https://arxiv.org/abs/1110.3304v3

import Mathlib

/-!
Statements from Wagemann--Wockel, arXiv:1110.3304v3.
The definitions below implement Definition VI.1 on an arbitrary category.
No additive structure on the source category and no left exactness at H^0
are imposed. The topological cohomology models are deferred in HARD.md.
-/

universe u v w

namespace QAlgorithms.Papers.Independent.Support21.P02

open CategoryTheory

/-- Definition VI.1, PDF p. 24: a category with distinguished composable
pairs. There are no exact-category axioms on the source category. -/
structure SequenceClass (C : Type u) [Category.{v} C] where
  distinguished : {A B D : C} → (A ⟶ B) → (B ⟶ D) → Prop

/-- Definition VI.1, PDF p. 24: one distinguished sequence A -> B -> D. -/
structure DistinguishedSequence {C : Type u} [Category.{v} C]
    (S : SequenceClass C) where
  A : C
  B : C
  D : C
  first : A ⟶ B
  second : B ⟶ D
  admissible : S.distinguished first second

/-- Definition VI.1, PDF pp. 24--25: the two commuting squares of a
morphism between distinguished sequences. -/
structure SequenceMap {C : Type u} [Category.{v} C] {S : SequenceClass C}
    (s t : DistinguishedSequence S) where
  left : s.A ⟶ t.A
  middle : s.B ⟶ t.B
  right : s.D ⟶ t.D
  first_square : s.first ≫ middle = left ≫ t.first
  second_square : s.second ≫ right = middle ≫ t.second

/-- Definition VI.1, PDF pp. 24--25: exactness of two abelian-group
homomorphisms at their common object, with no assertion at either end. -/
def ExactPair {A B D : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup D] (f : A →+ B) (g : B →+ D) : Prop :=
  ∀ b, g b = 0 ↔ ∃ a, f a = b

/-- Sanity: exactness at B in B --id--> B --0--> B does not assert
injectivity of the first arrow of an arbitrary long sequence. -/
example : ExactPair (AddMonoidHom.id ℤ) (0 : ℤ →+ ℤ) := by
  intro b
  simp

/-- Definition VI.1, PDF pp. 24--25: a cohomological delta-functor.
The three exactness clauses encode the long exact sequence, including
H^0(B) and H^0(D); exactness at H^0(A) is deliberately not required
(footnote 18). Connecting maps are natural for every sequence map. -/
structure DeltaFunctor {C : Type u} [Category.{v} C] (S : SequenceClass C) where
  degree : ℕ → C ⥤ AddCommGrpCat.{w}
  connecting : (s : DistinguishedSequence S) → (n : ℕ) →
    (degree n).obj s.D ⟶ (degree (n + 1)).obj s.A
  exact_middle : ∀ (s : DistinguishedSequence S) (n : ℕ), ExactPair
    ((degree n).map s.first).hom ((degree n).map s.second).hom
  exact_right : ∀ (s : DistinguishedSequence S) (n : ℕ), ExactPair
    ((degree n).map s.second).hom (connecting s n).hom
  exact_left_positive : ∀ (s : DistinguishedSequence S) (n : ℕ), ExactPair
    (connecting s n).hom ((degree (n + 1)).map s.first).hom
  connecting_natural : ∀ (s t : DistinguishedSequence S) (f : SequenceMap s t) n,
    (degree n).map f.right ≫ connecting t n =
      connecting s n ≫ (degree (n + 1)).map f.left

/-- Definition VI.1, PDF p. 25: a degreewise natural family, before any
compatibility with connecting maps is imposed. -/
structure DegreeFamily {C : Type u} [Category.{v} C] {S : SequenceClass C}
    (H K : DeltaFunctor.{u, v, w} S) where
  component : (n : ℕ) → H.degree n ⟶ K.degree n

/-- Definition VI.1, PDF p. 25, diagram (16). -/
def CommutesConnecting {C : Type u} [Category.{v} C] {S : SequenceClass C}
    {H K : DeltaFunctor.{u, v, w} S} (phi : DegreeFamily H K)
    (s : DistinguishedSequence S) (n : ℕ) : Prop :=
  H.connecting s n ≫ (phi.component (n + 1)).app s.A =
    (phi.component n).app s.D ≫ K.connecting s n

/-- Sanity: identity natural transformations commute with every actual
connecting map, regardless of the distinguished class. -/
example {C : Type u} [Category.{v} C] {S : SequenceClass C}
    (H : DeltaFunctor.{u, v, w} S) (s : DistinguishedSequence S) (n : ℕ) :
    CommutesConnecting (H := H) (K := H)
      ({ component := fun k => 𝟙 (H.degree k) } : DegreeFamily H H) s n := by
  simp [CommutesConnecting]

/-- Definition VI.1, PDF p. 25: a morphism of delta-functors. -/
structure DeltaMorphism {C : Type u} [Category.{v} C] {S : SequenceClass C}
    (H K : DeltaFunctor.{u, v, w} S) extends DegreeFamily H K where
  commutes : ∀ s n, CommutesConnecting toDegreeFamily s n

/-- Definition VI.1, PDF p. 25: mutually inverse delta-functor morphisms,
including their inverse identities as natural transformations. -/
structure DeltaEquivalence {C : Type u} [Category.{v} C] {S : SequenceClass C}
    (H K : DeltaFunctor.{u, v, w} S) where
  forward : DeltaMorphism H K
  backward : DeltaMorphism K H
  forward_backward : ∀ n,
    forward.component n ≫ backward.component n = 𝟙 (H.degree n)
  backward_forward : ∀ n,
    backward.component n ≫ forward.component n = 𝟙 (K.degree n)

/-- Theorem VI.2, PDF p. 25: the natural distinguished sequences used
for dimension shifting. These are the theorem's supplied I,U,iota,zeta,
not resolutions assumed to have any comparison maps. -/
structure FunctorialResolution {C : Type u} [Category.{v} C]
    (S : SequenceClass C) where
  I : C ⥤ C
  U : C ⥤ C
  iota : 𝟭 C ⟶ I
  zeta : I ⟶ U
  admissible : ∀ A, S.distinguished (iota.app A) (zeta.app A)

/-- Theorem VI.2, PDF p. 25: the distinguished sequence at A. -/
def FunctorialResolution.sequence {C : Type u} [Category.{v} C]
    {S : SequenceClass C} (R : FunctorialResolution S) (A : C) :
    DistinguishedSequence S where
  A := A
  B := R.I.obj A
  D := R.U.obj A
  first := R.iota.app A
  second := R.zeta.app A
  admissible := R.admissible A

/-- Sanity: the source of the resolution sequence is the original object. -/
example {C : Type u} [Category.{v} C] {S : SequenceClass C}
    (R : FunctorialResolution S) (A : C) : (R.sequence A).A = A := rfl

/-- Theorem VI.2(2), PDF p. 25: existence of Q_f, beta_f, gamma_f
with the distinguished lower sequence and both diagrams (17).
The unrecorded leftmost square in the first diagram is exactly naturality
of iota, which is already a field of the natural transformation R.iota. -/
def CompatibleQuotients {C : Type u} [Category.{v} C] {S : SequenceClass C}
    (R : FunctorialResolution S) : Prop :=
  ∀ s : DistinguishedSequence S,
    ∃ (Q : C) (q : R.I.obj s.B ⟶ Q)
      (beta : R.U.obj s.A ⟶ Q) (gamma : s.D ⟶ Q),
      S.distinguished (s.first ≫ R.iota.app s.B) q ∧
      R.zeta.app s.A ≫ beta = R.I.map s.first ≫ q ∧
      s.second ≫ gamma = R.iota.app s.B ≫ q

/-- Theorem VI.2(1), PDF p. 25: a family with exactly degrees 0,...,m.
There are no components in degrees greater than m. -/
structure FiniteFamily {C : Type u} [Category.{v} C] {S : SequenceClass C}
    (H K : DeltaFunctor.{u, v, w} S) (m : ℕ) where
  component : (n : ℕ) → n ≤ m → (H.degree n ⟶ K.degree n)

/-- Theorem VI.2(1), PDF p. 25: the resolution connecting squares in
precisely the finite range n < m. -/
def FiniteResolutionExtension {C : Type u} [Category.{v} C] {S : SequenceClass C}
    {H K : DeltaFunctor.{u, v, w} S} (R : FunctorialResolution S)
    {m : ℕ} (alpha : H.degree 0 ⟶ K.degree 0)
    (phi : FiniteFamily H K m) : Prop :=
  phi.component 0 (Nat.zero_le m) = alpha ∧
    ∀ (A : C) (n : ℕ) (hn : n < m),
      H.connecting (R.sequence A) n ≫
          (phi.component (n + 1) (Nat.succ_le_of_lt hn)).app A =
        (phi.component n (Nat.le_of_lt hn)).app (R.U.obj A) ≫
          K.connecting (R.sequence A) n

/-- Theorem VI.2(2), PDF p. 25: all distinguished-sequence connecting
squares, restricted to the range for which both components exist. -/
def FiniteConnectingCompatibility {C : Type u} [Category.{v} C]
    {S : SequenceClass C} {H K : DeltaFunctor.{u, v, w} S}
    {m : ℕ} (phi : FiniteFamily H K m) : Prop :=
  ∀ (s : DistinguishedSequence S) (n : ℕ) (hn : n < m),
    H.connecting s n ≫ (phi.component (n + 1) (Nat.succ_le_of_lt hn)).app s.A =
      (phi.component n (Nat.le_of_lt hn)).app s.D ≫ K.connecting s n

/-- Theorem VI.2, PDF pp. 25--26: the all-degree resolution squares. -/
def ResolutionExtension {C : Type u} [Category.{v} C] {S : SequenceClass C}
    {H K : DeltaFunctor.{u, v, w} S} (R : FunctorialResolution S)
    (alpha : H.degree 0 ⟶ K.degree 0) (phi : DegreeFamily H K) : Prop :=
  phi.component 0 = alpha ∧ ∀ A n, CommutesConnecting phi (R.sequence A) n

/-- Sanity: in the finite range m=0, only the initial transformation is
specified. No connecting square or positive-degree component is present. -/
example {C : Type u} [Category.{v} C] {S : SequenceClass C}
    {H K : DeltaFunctor.{u, v, w} S} (R : FunctorialResolution S)
    (alpha : H.degree 0 ⟶ K.degree 0) (phi : FiniteFamily H K 0) :
    FiniteResolutionExtension R alpha phi ↔ phi.component 0 (Nat.zero_le 0) = alpha := by
  simp [FiniteResolutionExtension]

end QAlgorithms.Papers.Independent.Support21.P02


