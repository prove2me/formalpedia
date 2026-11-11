-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_ActionAssertions
-- name    : FiniteGroupTesting_LinearQuery_ActionAssertions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:09:46.141054+00:00
-- url     : https://prove2.me/theorems/8083415a-89c9-4f9e-9c36-d36e6b3edf2d
-- title:
--   Block partitions and subgroup assertions for reached executions
-- statement:
--   These mathematical predicates state the Algorithm 1 input assumptions, its disjoint block partition, the blockwise lift of a permutation, subgroup closure under a supplied multiplication, and the generated subgroup. The input requires a valid stored transitive action, $e\in H$ and $b\notin H$; it makes no group promise about the unknown table.
--
--   $$D=\bigsqcup_{t\in T}\mu_t(H),\qquad\widehat q(\mu_t(c))=\mu_t(q(c)).$$
--
--   Generated elements are obtained from the specified set and identity by multiplication and two-sided inversion. An honest action is the actual left-regular action of the supplied group on its subgroup, extended by identity outside. These are assertion definitions only: no algorithm output is required to carry their truth, and reached-state hypotheses are supplied explicitly in the theorem statements.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 15–19, §3.1, Lemmas 3.2–3.7

import Definitions.Def_FiniteGroupTesting_LinearQuery_Tester

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery

attribute [local instance] Classical.propDecidable

def ExtensionInput {n : ℕ} (a : StoredAction n) (e b : Fin n) : Prop :=
  a.Valid ∧ e ∈ a.domain.carrier ∧ b ∉ a.domain.carrier ∧
    TransitiveOn a.group a.domain.carrier

def blockSet {n : ℕ} (a : StoredAction n) (s : ExtensionState n) (t : Fin n) :
    Finset (Fin n) := a.domain.carrier.image (s.chart t)

def BlockPartition {n : ℕ} (a : StoredAction n) (e : Fin n) (s : ExtensionState n) : Prop :=
  s.discovered.carrier = s.representatives.carrier.biUnion (blockSet a s) ∧
  (∀ t ∈ s.representatives.carrier,
    Set.BijOn (s.chart t) (a.domain.carrier : Set (Fin n)) (blockSet a s t : Set (Fin n)) ∧
      s.chart t e = t) ∧
  (∀ t ∈ s.representatives.carrier, ∀ u ∈ s.representatives.carrier,
    t ≠ u → Disjoint (blockSet a s t) (blockSet a s u))

/-- The blockwise extension, with identity on unused ambient labels. -/
def blockLift {n : ℕ} (s : ExtensionState n) (q : Equiv.Perm (Fin n)) (x : Fin n) : Fin n :=
  if s.discovered.marked x then s.chart (s.block x) (q (s.coordinate x)) else x

def SubgroupFor {X : Type*} (op : X → X → X) (e : X) (S : Set X) : Prop :=
  e ∈ S ∧ (∀ x ∈ S, ∀ y ∈ S, op x y ∈ S) ∧
    ∀ x ∈ S, ∃ y ∈ S, op x y = e ∧ op y x = e

/-- The subgroup generated under the supplied operation; no operation is an unrelated variable. -/
inductive Generated {X : Type*} (op : X → X → X) (e : X) (S : Set X) : X → Prop
  | identity : Generated op e S e
  | base (x : X) : x ∈ S → Generated op e S x
  | mul (x y : X) : Generated op e S x → Generated op e S y → Generated op e S (op x y)
  | inv (x y : X) : Generated op e S x → op x y = e → op y x = e → Generated op e S y

/-- Restriction of the full group axioms to a set, retaining a total ambient operation. -/
def GroupLawOn {X : Type*} (op : X → X → X) (e : X) (S : Set X) : Prop :=
  SubgroupFor op e S ∧
  (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, op (op x y) z = op x (op y z)) ∧
  (∀ x ∈ S, op e x = x) ∧ (∀ x ∈ S, op x e = x)

def TrueLeftAction {n : ℕ} [Group (Fin n)] (H : Subgroup (Fin n))
    (P : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∀ p : Equiv.Perm (Fin n), p ∈ P ↔
    ∃ h : H, ∀ x : Fin n, p x = if x ∈ H then h.val * x else x

end FiniteGroupTesting.LinearQuery


