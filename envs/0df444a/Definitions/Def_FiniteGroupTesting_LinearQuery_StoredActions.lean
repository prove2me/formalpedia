-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_StoredActions
-- name    : FiniteGroupTesting_LinearQuery_StoredActions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:55.251327+00:00
-- url     : https://prove2.me/theorems/63fe63f8-6c16-43cf-9e15-0b8e73d6798f
-- title:
--   Explicit generator tables and induced group operation
-- statement:
--   An indexed set stores its live label count, its distinct labels and membership marks. An action stores generator images on that set, with identity images on unused ambient labels. Validity means these raw stored images are permutations; it does not mean the action is regular. Let $P$ be their generated subgroup of the actual symmetric group. Transitivity requires a permutation sending each point to any other; regularity requires exactly one.
--
--   $$x\circ y=p_x(y),\qquad p_x(e)=x,\quad p_x\in P.$$
--
--   The mathematical representative selector chooses such a permutation when it exists and the identity otherwise. It is used only to state induced group laws. The algorithm uses charged orbit-tree evaluation rather than this noncomputable selector. Indexed arrays describe RAM cells, with functional updates denoting cell writes.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 13, 15–16, §2.2 and Algorithm 1 data

import Definitions.Def_FiniteGroupTesting_LinearQuery_OracleRuns

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery

attribute [local instance] Classical.propDecidable

/-- Indexed RAM storage. Only cells below count are live; outside cells have a harmless default.
Functional updates describe writes to an indexed RAM cell, not persistent-list copying. -/
structure LabelSet (n : ℕ) where
  count : ℕ
  labels : ℕ → Fin n
  marked : Fin n → Bool

namespace LabelSet

def empty {n : ℕ} (e : Fin n) : LabelSet n := ⟨0, fun _ => e, fun _ => false⟩

def insert {n : ℕ} (s : LabelSet n) (x : Fin n) : LabelSet n :=
  ⟨s.count + 1, Function.update s.labels s.count x, Function.update s.marked x true⟩

def carrier {n : ℕ} (s : LabelSet n) : Finset (Fin n) :=
  (Finset.range s.count).image s.labels

def Valid {n : ℕ} (s : LabelSet n) : Prop :=
  s.count ≤ n ∧ (∀ x, s.marked x = true ↔ x ∈ s.carrier) ∧
    Set.InjOn s.labels {i | i < s.count}

end LabelSet

/-- Explicitly stored generator images, indexed by generator number and label. -/
structure StoredAction (n : ℕ) where
  domain : LabelSet n
  degree : ℕ
  image : ℕ → Fin n → Fin n

/-- Valid stored permutations fix unused labels, so restriction to the domain is faithful. -/
def StoredAction.Valid {n : ℕ} (a : StoredAction n) : Prop :=
  a.domain.Valid ∧ ∀ i < a.degree,
    Function.Bijective (a.image i) ∧ ∀ x ∉ a.domain.carrier, a.image i x = x

noncomputable def storedPermutation {n : ℕ} (f : Fin n → Fin n) : Equiv.Perm (Fin n) :=
  if h : Function.Bijective f then Equiv.ofBijective f h else Equiv.refl _

noncomputable def StoredAction.group {n : ℕ} (a : StoredAction n) :
    Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {p | ∃ i < a.degree, p = storedPermutation (a.image i)}

def TransitiveOn {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n)))
    (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃ p : P, p.val x = y

def RegularOn {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n)))
    (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃! p : P, p.val x = y

/-- Unique representative when it exists; identity otherwise. Used only mathematically.
The tester uses its orbit-tree words, not this noncomputable selector. -/
noncomputable def representative {X : Type*} (P : Subgroup (Equiv.Perm X))
    (e x : X) : P :=
  if h : ∃ p : P, p.val e = x then Classical.choose h else 1

noncomputable def inducedLaw {X : Type*} (P : Subgroup (Equiv.Perm X))
    (e : X) (x y : X) : X := (representative P e x).val y

/-- Regularity of an actual permutation subgroup on its entire carrier. -/
def Regular {X : Type*} (P : Subgroup (Equiv.Perm X)) : Prop :=
  ∀ x y : X, ∃! p : P, p.val x = y

end FiniteGroupTesting.LinearQuery


