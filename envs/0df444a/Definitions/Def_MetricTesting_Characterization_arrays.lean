-- Prove2me | Definitions.Def_MetricTesting_Characterization_arrays
-- name    : MetricTesting_Characterization_arrays
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:51.093748+00:00
-- url     : https://prove2.me/theorems/3cb5816f-ab20-4ffd-b6db-0e90a1b09f05
-- title:
--   Local matrix framework, valid arrays, violation packing and repair distance
-- statement:
--   Fix an integer $k\ge2$ and a nonempty set $\Lambda\subseteq\mathbb R_{\ge0}$. An array $D$ assigns a value in $\Lambda$ to every unordered distinct pair of $n$ labels; diagonal entries are fixed separately to zero. A permutation-invariant predicate $\Phi$ on $k$ labels determines $\mathcal P_n$: every $k$-point restriction must satisfy $\Phi$. Thus every array of order $n<k$ is valid. Nonempty targets at orders $n\ge k$ and extendability are separate predicates. Extendability asks for a valid larger array containing the given valid array along some injection.
--
--   Let $V(D)$ be the violating $k$-subsets and let $\nu(D)$ be the maximum size of a family of them sharing no edge. Sharing a vertex is allowed. Define
--   $$\operatorname{viol}(D)=\frac{|V(D)|}{\binom nk},\qquad d(D,\mathcal P_n)=\frac2{n^2}\min_{B\in\mathcal P_n}|\{e:D_e\ne B_e\}|.$$
--   The minimum is attained because its possible discrepancy counts form a nonempty subset of a finite set. This interface separates the input class from the structural conclusions and does not assert the triangle inequality. The measurable-predicate condition uses the usual finite product of inherited Borel spaces on $\Lambda$.
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), pp. 5–6, §2 and Definitions 2.1, 2.3 (PDF pp. 6–7); p. 10, Definition 3.5 (PDF p. 11)

import Mathlib

set_option autoImplicit false

noncomputable section

namespace MetricTesting.Characterization

/-- Unordered distinct pairs. The diagonal is separately fixed to zero. -/
abbrev Edge (n : ℕ) := {s : Finset (Fin n) // s.card = 2}

abbrev Array (Λ : Set NNReal) (n : ℕ) := Edge n → Λ

/-- Transport an edge along an injection; no ordering of endpoints is retained. -/
def edgeMap {r n : ℕ} (f : Fin r ↪ Fin n) (e : Edge r) : Edge n :=
  ⟨e.1.map f, by simpa using e.2⟩

def restrictArray {Λ : Set NNReal} {r n : ℕ} (D : Array Λ n)
    (f : Fin r ↪ Fin n) : Array Λ r := fun e => D (edgeMap f e)

/-- Section 2's fixed local predicate, before any structural assumptions. -/
structure LocalData where
  k : ℕ
  arity : 2 ≤ k
  values : Set NNReal
  values_nonempty : values.Nonempty
  predicate : Set (Array values k)
  invariant : ∀ (D : Array values k) (σ : Equiv.Perm (Fin k)),
    restrictArray D σ.toEmbedding ∈ predicate ↔ D ∈ predicate

/-- Every injection supplies one labelled k-point restriction. -/
def Valid (F : LocalData) {n : ℕ} (D : Array F.values n) : Prop :=
  ∀ f : Fin F.k ↪ Fin n, restrictArray D f ∈ F.predicate

/-- The standing nonempty-target assumption, not a structural conclusion. -/
def TargetsNonempty (F : LocalData) : Prop :=
  ∀ n : ℕ, F.k ≤ n → ∃ D : Array F.values n, Valid F D

def Extendable (F : LocalData) : Prop :=
  ∀ r n : ℕ, F.k ≤ r → r ≤ n → ∀ A : Array F.values r,
    Valid F A → ∃ B : Array F.values n, Valid F B ∧
      ∃ f : Fin r ↪ Fin n, restrictArray B f = A

/-- Usual product of inherited Borel sigma algebras, without regularity of Λ. -/
def PredicateMeasurable (F : LocalData) : Prop := MeasurableSet F.predicate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A k-set violates iff at least one labelling violates; invariance makes
this equivalent to failure in every labelling. -/
def Violations (F : LocalData) {n : ℕ} (D : Array F.values n) :
    Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S => S.card = F.k ∧
    ∃ f : Fin F.k ↪ Fin n,
      Finset.univ.map f = S ∧ restrictArray D f ∉ F.predicate

def violationDensity (F : LocalData) {n : ℕ} (D : Array F.values n) : ℝ :=
  (Violations F D).card / (Nat.choose n F.k : ℝ)

def discrepancy {Λ : Set NNReal} {n : ℕ} (D B : Array Λ n) : ℕ :=
  (Finset.univ.filter fun e => D e ≠ B e).card

/-- Nat.find is an attained minimum, with a total zero fallback outside the
nonempty-target domain. All theorem uses have nonempty targets. -/
def minimumEdits (F : LocalData) {n : ℕ} (D : Array F.values n) : ℕ :=
  if h : ∃ m : ℕ, ∃ B : Array F.values n, Valid F B ∧ discrepancy D B = m
  then Nat.find h else 0

def repairDistance (F : LocalData) {n : ℕ} (D : Array F.values n) : ℝ :=
  2 * minimumEdits F D / (n : ℝ)^2

def EdgeDisjoint {n : ℕ} (S : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ e : Edge n, ¬ (e.1 ⊆ A ∧ e.1 ⊆ B)

/-- Maximum over the finite powerset includes the empty packing. -/
def packingNumber (F : LocalData) {n : ℕ} (D : Array F.values n) : ℕ :=
  (((Violations F D).powerset.filter EdgeDisjoint).image Finset.card).max'
    (by
      refine ⟨0, Finset.mem_image.mpr ⟨∅, ?_, rfl⟩⟩
      simp [EdgeDisjoint])

end MetricTesting.Characterization


