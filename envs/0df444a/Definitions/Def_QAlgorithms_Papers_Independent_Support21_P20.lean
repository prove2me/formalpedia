-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
-- name    : QAlgorithms_Papers_Independent_Support21_P20
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T04:54:48.435615+00:00
-- url     : https://prove2.me/theorems/43557362-bf3c-4065-a7ec-117177db6c3d
-- title:
--   Definitions for Gelfand-type duality for commutative von Neumann algebras
-- statement:
--   The objects the formalized statements of *Gelfand-type duality for commutative von Neumann algebras* (arXiv:2005.05284) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsValuation`: Definition 2.19, PDF p.10: the modular and zero axioms of a valuation.
--   - `PreservesDirectedSuprema`: Definition 2.19, PDF p.10: continuity only at existing directed suprema.
--   - `IsPositiveContinuousValuation`: Definition 2.19, PDF p.10: finite positive continuous valuations.
--   - `IsContinuousValuation`: Definition 2.19, PDF p.10: the directed net, including its actual limit.
--   - `IsCompletelyAdditiveValuation`: Definition 2.20, PDF p.10: arbitrary small families, including empty ones. `HasSum` demands convergence, so an undefined `tsum` cannot certify additivity.
--   - `IsCoherentLocale`: Definition 2.25, PDF p.11, with the empty finite meet included.
--   - `IsRegularLocale`: Definition 2.35, PDF p.13: regularity of the frame of opens.
--   - `IsStoneLocale`: Definition 2.35, PDF p.13: Stone means regular and coherent.
--   - `IsStoneanLocale`: Definition 2.45, PDF p.15: the Stonean condition.
--   - `IsBooleanLocale`: Lemma 2.44, PDF pp.14–15: Boolean frames, allowing the one-element frame.
--   - `HasFiniteValuationCover`: Definition 2.52, PDF p.17: enough faithful finite principal parts. The interval `Iic a` is the underlying order of the principal algebra aA. This is an unmeasured object predicate. The accepted Renew46.P02 predicate `IsLocalizableBoolean` instead takes a chosen Boolean measure; it is not a direct replacement for this source definition.
--   - `IsNormalValuation`: Definition 2.57, PDF p.18: finite real or complex normal valuations.
--   - `IsPositiveNormalValuation`: Definition 2.57, PDF p.18: positive normal valuations.
--   - `IsJordanRegime`: Lemma 2.59, PDF p.18: the two regimes explicitly covered by the lemma.
--   - `positiveCarrier`: Lemma 2.59, PDF p.18: maximal carrier of positivity, computed as a supremum.
--   - `negativeCarrier`: Lemma 2.59, PDF p.18: maximal carrier of negativity.
--   - `jordanPositive`: Lemma 2.59, PDF p.18: positive part without clamping its real value.
--   - `jordanNegative`: Lemma 2.59, PDF p.18: the minus sign in the negative part.
--   - `valuationVariation`: Lemma 2.59, PDF p.18: total variation as the sum of the two positive parts.
--   - `valuationVariationNorm`: Lemma 2.59, PDF p.18: variation norm is variation evaluated at the top.
--   - `HahnJordanConclusions`: Lemma 2.59, PDF pp.18–19: all real Hahn–Jordan conclusions.
--   - `ComplexJordanConclusions`: Lemma 2.59, PDF pp.18–19: the canonical four complex summands.
--   - `PreservesSuprema`: Definition 2.43, PDF p.14: completeness of a map between complete Boolean algebras.
--   - `IsSigmaAlgebra`: Definition 4.2, PDF p.29: a sigma-algebra of subsets.
--   - `IsCompleteSigmaIdeal`: Definitions 4.3–4.4, PDF p.29: a complete sigma-ideal of all subsets.
--   - `Enhanced`: Definition 4.4, PDF p.29: complete enhanced measurable spaces.
--   - `partialDomain`: Definition 4.6, PDF p.29: the point-set domain includes every defined point.
--   - `partialPreimage`: Definition 4.6, PDF p.29: undefined points contribute nothing to preimages.
--   - `IsPremap`: Definition 4.6, PDF p.29: partial premaps reflect negligible subsets.
--   - `Premap`: Definition 4.6, PDF p.29: a premap carries its actual partial function.
--   - `partialCompose`: Proposition 4.7, PDF p.29: composition restricts the domain by `Option.bind`.
--   - `StrictAE`: Definition 4.11, PDF p.30: defined versus undefined is a disagreement.
--   - `WeakAE`: Definition 4.13, PDF pp.30–31: weak equality tests every target measurable set.
--   - `strictHomRelation`: The strict hom relation of Definition 4.11, PDF p.30.
--   - `weakHomRelation`: The weak hom relation of Definition 4.13, PDF pp.30–31.
--   - `IsCountablySeparated`: Definition 4.21, PDF p.32: countable separation includes a covering condition.
--   - `IsCompactClassOn`: Definition 4.57, PDF p.37: intersections relative to an ambient measurable subset. The empty finite subfamily intersects to that ambient subset.
--   - `IsCompactEnhancedOn`: Definitions 4.5 and 4.57, PDF pp.29,37: compactness of the induced space on m. Subsets of m are represented as ambient subsets contained in m.
--   - `nullEnhanced`: An entirely negligible space, allowed by Definition 4.4, PDF p.29.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, https://arxiv.org/abs/2005.05284v3

import Mathlib

/-!
Statements from Pavlov, arXiv:2005.05284v3. New definitions are confined to
this paper. Locales are represented by their frames of opens. All functions
called valuations below have finite values. No nontriviality is imposed.
-/

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter
open scoped NNReal

universe u v

/-- Definition 2.19, PDF p.10: the modular and zero axioms of a valuation. -/
def IsValuation {A R : Type*} [Lattice A] [OrderBot A] [Zero R] [Add R]
    (nu : A → R) : Prop :=
  nu ⊥ = 0 ∧ ∀ a b, nu a + nu b = nu (a ⊔ b) + nu (a ⊓ b)

/-- Definition 2.19, PDF p.10: continuity only at existing directed suprema. -/
def PreservesDirectedSuprema {A : Type*} [PartialOrder A] (nu : A → ℝ≥0) : Prop :=
  ∀ (s : Set A) (a : A), s.Nonempty → DirectedOn (· ≤ ·) s →
    IsLUB s a → IsLUB (nu '' s) (nu a)

/-- Definition 2.19, PDF p.10: finite positive continuous valuations. -/
def IsPositiveContinuousValuation {A : Type*} [Lattice A] [OrderBot A]
    (nu : A → ℝ≥0) : Prop :=
  IsValuation nu ∧ Monotone nu ∧ PreservesDirectedSuprema nu

/-- Definition 2.19, PDF p.10: the directed net, including its actual limit. -/
def IsContinuousValuation {A R : Type*} [Lattice A] [OrderBot A]
    [Zero R] [Add R] [TopologicalSpace R] (nu : A → R) : Prop :=
  IsValuation nu ∧ ∀ (s : Set A) (a : A), s.Nonempty →
    DirectedOn (· ≤ ·) s → IsLUB s a →
    Tendsto (fun b : s => nu b.val) atTop (nhds (nu a))

/-- Definition 2.20, PDF p.10: arbitrary small families, including empty ones.
`HasSum` demands convergence, so an undefined `tsum` cannot certify additivity. -/
def IsCompletelyAdditiveValuation {A : Type u} [CompleteBooleanAlgebra A]
    (nu : A → ℝ≥0) : Prop :=
  IsValuation nu ∧ Monotone nu ∧ ∀ (I : Type u) (x : I → A),
    (∀ i j, i ≠ j → x i ⊓ x j = ⊥) → HasSum (fun i => nu (x i)) (nu (iSup x))

/-- Definition 2.25, PDF p.11, with the empty finite meet included. -/
def IsCoherentLocale (L : Type*) [Order.Frame L] : Prop :=
  IsCompactElement (⊤ : L) ∧
  (∀ a b : L, IsCompactElement a → IsCompactElement b → IsCompactElement (a ⊓ b)) ∧
  ∀ a : L, a = sSup {b : L | IsCompactElement b ∧ b ≤ a}

/-- Definition 2.35, PDF p.13: regularity of the frame of opens. -/
def IsRegularLocale (L : Type*) [Order.Frame L] : Prop :=
  ∀ a : L, a = sSup {b : L | bᶜ ⊔ a = ⊤}

/-- Definition 2.35, PDF p.13: Stone means regular and coherent. -/
def IsStoneLocale (L : Type*) [Order.Frame L] : Prop :=
  IsCoherentLocale L ∧ IsRegularLocale L

/-- Definition 2.45, PDF p.15: the Stonean condition. -/
def IsStoneanLocale (L : Type*) [Order.Frame L] : Prop :=
  IsStoneLocale L ∧ ∀ a : L, aᶜ ⊔ aᶜᶜ = ⊤

/-- Lemma 2.44, PDF pp.14–15: Boolean frames, allowing the one-element frame. -/
def IsBooleanLocale (L : Type*) [Order.Frame L] : Prop :=
  ∀ a : L, a ⊔ aᶜ = ⊤

/-- Definition 2.52, PDF p.17: enough faithful finite principal parts.
The interval `Iic a` is the underlying order of the principal algebra aA.
This is an unmeasured object predicate. The accepted Renew46.P02 predicate
`IsLocalizableBoolean` instead takes a chosen Boolean measure; it is not a
direct replacement for this source definition. -/
def HasFiniteValuationCover (A : Type*) [CompleteBooleanAlgebra A] : Prop :=
  sSup {a : A | ∃ nu : Set.Iic a → ℝ≥0,
    IsPositiveContinuousValuation nu ∧ ∀ b, nu b = 0 → b = ⊥} = ⊤

/-- Definition 2.57, PDF p.18: finite real or complex normal valuations. -/
def IsNormalValuation {L R : Type*} [Order.Frame L] [Zero R] [Add R]
    [TopologicalSpace R] (nu : L → R) : Prop :=
  IsContinuousValuation nu ∧ ∀ a, nu aᶜᶜ = nu a

/-- Definition 2.57, PDF p.18: positive normal valuations. -/
def IsPositiveNormalValuation {L : Type*} [Order.Frame L] (nu : L → ℝ≥0) : Prop :=
  IsPositiveContinuousValuation nu ∧ ∀ a, nu aᶜᶜ = nu a

/-- Lemma 2.59, PDF p.18: the two regimes explicitly covered by the lemma. -/
def IsJordanRegime {L R : Type*} [Order.Frame L] [Zero R] [Add R]
    [TopologicalSpace R] (nu : L → R) : Prop :=
  (IsStoneanLocale L ∧ IsNormalValuation nu) ∨
  (IsBooleanLocale L ∧ IsContinuousValuation nu)

/-- Lemma 2.59, PDF p.18: maximal carrier of positivity, computed as a supremum. -/
def positiveCarrier {L : Type*} [Order.Frame L] (nu : L → ℝ) : L :=
  sSup {a : L | ∀ b : L, b ≤ a → 0 ≤ nu b}

/-- Lemma 2.59, PDF p.18: maximal carrier of negativity. -/
def negativeCarrier {L : Type*} [Order.Frame L] (nu : L → ℝ) : L :=
  positiveCarrier (fun a => -nu a)

/-- Lemma 2.59, PDF p.18: positive part without clamping its real value. -/
def jordanPositive {L : Type*} [Order.Frame L] (nu : L → ℝ) (a : L) : ℝ :=
  nu (positiveCarrier nu ⊓ a)

/-- Lemma 2.59, PDF p.18: the minus sign in the negative part. -/
def jordanNegative {L : Type*} [Order.Frame L] (nu : L → ℝ) (a : L) : ℝ :=
  -nu (negativeCarrier nu ⊓ a)

/-- Lemma 2.59, PDF p.18: total variation as the sum of the two positive parts. -/
def valuationVariation {L : Type*} [Order.Frame L] (nu : L → ℝ) (a : L) : ℝ :=
  jordanPositive nu a + jordanNegative nu a

/-- Lemma 2.59, PDF p.18: variation norm is variation evaluated at the top. -/
def valuationVariationNorm {L : Type*} [Order.Frame L] (nu : L → ℝ) : ℝ :=
  valuationVariation nu ⊤

/-- Lemma 2.59, PDF pp.18–19: all real Hahn–Jordan conclusions. -/
def HahnJordanConclusions {L : Type*} [Order.Frame L] (nu : L → ℝ) : Prop :=
  (∀ a, (∀ b, b ≤ a → 0 ≤ nu b) ↔ a ≤ positiveCarrier nu) ∧
  (∀ a, (∀ b, b ≤ a → 0 ≤ -nu b) ↔ a ≤ negativeCarrier nu) ∧
  positiveCarrier nu ⊔ negativeCarrier nu = ⊤ ∧
  (∀ a, (∀ b, b ≤ a → nu b = 0) ↔
    a ≤ positiveCarrier nu ⊓ negativeCarrier nu) ∧
  IsNormalValuation (jordanPositive nu) ∧
  IsNormalValuation (jordanNegative nu) ∧
  (∀ a, 0 ≤ jordanPositive nu a) ∧ (∀ a, 0 ≤ jordanNegative nu a) ∧
  ∀ a, nu a = jordanPositive nu a - jordanNegative nu a

/-- Lemma 2.59, PDF pp.18–19: the canonical four complex summands. -/
def ComplexJordanConclusions {L : Type*} [Order.Frame L] (nu : L → ℂ) : Prop :=
  let re := fun a => (nu a).re
  let im := fun a => (nu a).im
  HahnJordanConclusions re ∧ HahnJordanConclusions im ∧
  ∀ a, nu a =
    ((jordanPositive re a : ℂ) - (jordanNegative re a : ℂ)) +
    Complex.I * ((jordanPositive im a : ℂ) - (jordanNegative im a : ℂ))

/-- Definition 2.43, PDF p.14: completeness of a map between complete Boolean algebras. -/
def PreservesSuprema {A B : Type*} [CompleteLattice A] [CompleteLattice B]
    (f : A → B) : Prop := ∀ s : Set A, f (sSup s) = sSup (f '' s)

/-- Definition 4.2, PDF p.29: a sigma-algebra of subsets. -/
def IsSigmaAlgebra {X : Type*} (M : Set (Set X)) : Prop :=
  ∅ ∈ M ∧ (∀ a ∈ M, aᶜ ∈ M) ∧
  ∀ a : ℕ → Set X, (∀ i, a i ∈ M) → (⋃ i, a i) ∈ M

/-- Definitions 4.3–4.4, PDF p.29: a complete sigma-ideal of all subsets. -/
def IsCompleteSigmaIdeal {X : Type*} (N : Set (Set X)) : Prop :=
  ∅ ∈ N ∧ (∀ a b : Set X, a ⊆ b → b ∈ N → a ∈ N) ∧
  ∀ a : ℕ → Set X, (∀ i, a i ∈ N) → (⋃ i, a i) ∈ N

/-- Definition 4.4, PDF p.29: complete enhanced measurable spaces. -/
structure Enhanced (X : Type u) where
  measurable : Set (Set X)
  negligible : Set (Set X)
  sigmaAlgebra : IsSigmaAlgebra measurable
  sigmaIdeal : IsCompleteSigmaIdeal negligible
  negligibleMeasurable : negligible ⊆ measurable

/-- Definition 4.6, PDF p.29: the point-set domain includes every defined point. -/
def partialDomain {X Y : Type*} (f : X → Option Y) : Set X :=
  {x | ∃ y, f x = some y}

/-- Definition 4.6, PDF p.29: undefined points contribute nothing to preimages. -/
def partialPreimage {X Y : Type*} (f : X → Option Y) (s : Set Y) : Set X :=
  {x | ∃ y ∈ s, f x = some y}

/-- Definition 4.6, PDF p.29: partial premaps reflect negligible subsets. -/
def IsPremap {X Y : Type u} (E : Enhanced X) (F : Enhanced Y)
    (f : X → Option Y) : Prop :=
  (partialDomain f)ᶜ ∈ E.negligible ∧
  (∀ s ∈ F.measurable, partialPreimage f s ∈ E.measurable) ∧
  ∀ s ∈ F.negligible, partialPreimage f s ∈ E.negligible

/-- Definition 4.6, PDF p.29: a premap carries its actual partial function. -/
def Premap {X Y : Type u} (E : Enhanced X) (F : Enhanced Y) :=
  {f : X → Option Y // IsPremap E F f}

/-- Proposition 4.7, PDF p.29: composition restricts the domain by `Option.bind`. -/
def partialCompose {X Y Z : Type*} (g : Y → Option Z) (f : X → Option Y)
    (x : X) : Option Z := (f x).bind g

/-- Definition 4.11, PDF p.30: defined versus undefined is a disagreement. -/
def StrictAE {X Y : Type u} (E : Enhanced X) (f g : X → Option Y) : Prop :=
  {x | f x ≠ g x} ∈ E.negligible

/-- Definition 4.13, PDF pp.30–31: weak equality tests every target measurable set. -/
def WeakAE {X Y : Type u} (E : Enhanced X) (F : Enhanced Y)
    (f g : X → Option Y) : Prop :=
  ∀ s ∈ F.measurable,
    ((partialPreimage f s \ partialPreimage g s) ∪
      (partialPreimage g s \ partialPreimage f s)) ∈ E.negligible

/-- The strict hom relation of Definition 4.11, PDF p.30. -/
def strictHomRelation {X Y : Type u} (E : Enhanced X) (F : Enhanced Y)
    (f g : Premap E F) : Prop := StrictAE E f.val g.val

/-- The weak hom relation of Definition 4.13, PDF pp.30–31. -/
def weakHomRelation {X Y : Type u} (E : Enhanced X) (F : Enhanced Y)
    (f g : Premap E F) : Prop := WeakAE E F f.val g.val

/-- Definition 4.21, PDF p.32: countable separation includes a covering condition. -/
def IsCountablySeparated {X : Type u} (E : Enhanced X) : Prop :=
  ∃ S : Set (Set X), S.Countable ∧ S ⊆ E.measurable ∧
    (∀ x y : X, x ≠ y → ∃ s ∈ S, x ∈ s ∧ y ∉ s) ∧
    ∀ x : X, ∃ s ∈ S, x ∈ s

/-- Definition 4.57, PDF p.37: intersections relative to an ambient measurable subset.
The empty finite subfamily intersects to that ambient subset. -/
def IsCompactClassOn {X : Type*} (m : Set X) (K : Set (Set X)) : Prop :=
  ∀ T : Set (Set X), T ⊆ K →
    (∀ U : Set (Set X), U.Finite → U ⊆ T → (m ∩ ⋂₀ U).Nonempty) →
    (m ∩ ⋂₀ T).Nonempty

/-- Definitions 4.5 and 4.57, PDF pp.29,37: compactness of the induced space on m.
Subsets of m are represented as ambient subsets contained in m. -/
def IsCompactEnhancedOn {X : Type u} (E : Enhanced X) (m : Set X) : Prop :=
  ∃ K : Set (Set X), (∀ k ∈ K, k ⊆ m ∧ k ∈ E.measurable) ∧
    IsCompactClassOn m K ∧
    ∀ s : Set X, s ⊆ m → s ∈ E.measurable → s ∉ E.negligible →
      ∃ k ∈ K, k ⊆ s ∧ k ∉ E.negligible

/-- Sanity: the identity map preserves every supremum, including the empty one. -/
example {A : Type*} [CompleteLattice A] : PreservesSuprema (id : A → A) := by
  intro s
  simp

/-- Sanity: valuation modularity has the source's zero normalization. -/
example {A R : Type*} [Lattice A] [OrderBot A] [Zero R] [Add R] (nu : A → R) :
    IsValuation nu ↔ (nu ⊥ = 0 ∧ ∀ a b, nu a + nu b = nu (a ⊔ b) + nu (a ⊓ b)) := Iff.rfl

/-- Sanity: the negative Jordan part carries an actual minus sign. -/
example {L : Type*} [Order.Frame L] (nu : L → ℝ) (a : L) :
    jordanNegative nu a = -nu (negativeCarrier nu ⊓ a) := rfl

/-- Sanity: total identity premaps pull subsets back unchanged. -/
example {X : Type*} (s : Set X) : partialPreimage (fun x : X => some x) s = s := by
  ext x
  simp [partialPreimage]

/-- Sanity: there is no point in the point-set domain of the empty partial map. -/
example {X Y : Type*} : partialDomain (fun _ : X => (none : Option Y)) = ∅ := by
  ext x
  simp [partialDomain]

/-- Sanity: compactness within the empty induced space is vacuous, as required. -/
example {X : Type*} (K : Set (Set X)) : IsCompactClassOn (∅ : Set X) K := by
  intro T hT h
  have hbad := h ∅ Set.finite_empty (Set.empty_subset T)
  simpa using hbad

/-- Sanity: the zero valuation is normalized and modular on every lattice. -/
example {A : Type*} [Lattice A] [OrderBot A] :
    IsValuation (fun _ : A => (0 : ℝ≥0)) := by
  simp [IsValuation]

/-- Sanity: the zero signed valuation has both carriers equal to top, not disjoint. -/
example (L : Type*) [Order.Frame L] :
    positiveCarrier (fun _ : L => (0 : ℝ)) = ⊤ ∧
    negativeCarrier (fun _ : L => (0 : ℝ)) = ⊤ := by
  simp [positiveCarrier, negativeCarrier]

/-- Sanity: total variation and its norm vanish on the zero valuation. -/
example (L : Type*) [Order.Frame L] :
    valuationVariationNorm (fun _ : L => (0 : ℝ)) = 0 := by
  simp [valuationVariationNorm, valuationVariation, jordanPositive, jordanNegative]

/-- An entirely negligible space, allowed by Definition 4.4, PDF p.29. -/
def nullEnhanced (X : Type u) : Enhanced X where
  measurable := Set.univ
  negligible := Set.univ
  sigmaAlgebra := by simp [IsSigmaAlgebra]
  sigmaIdeal := by simp [IsCompleteSigmaIdeal]
  negligibleMeasurable := Set.Subset.rfl

/-- Sanity: a nonempty entirely negligible source has a premap into the empty target. -/
example : IsPremap (nullEnhanced PUnit) (nullEnhanced Empty)
    (fun _ : PUnit => (none : Option Empty)) := by
  simp [IsPremap, nullEnhanced]

/-- Sanity: the union of no separation tests cannot cover even the one-point space. -/
example : ¬ (∀ x : PUnit, ∃ s ∈ (∅ : Set (Set PUnit)), x ∈ s) := by
  simp

end QAlgorithms.Papers.Independent.Support21.P20


