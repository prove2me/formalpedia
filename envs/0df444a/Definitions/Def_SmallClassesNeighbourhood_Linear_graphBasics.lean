-- Prove2me | Definitions.Def_SmallClassesNeighbourhood_Linear_graphBasics
-- name    : SmallClassesNeighbourhood_Linear_graphBasics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:34:25.177772+00:00
-- url     : https://prove2.me/theorems/d588e2f2-af76-4439-99ef-db0e8465e73d
-- title:
--   Finite graph classes, traces, diversity and actual cores
-- statement:
--   A labelled graph class assigns a collection of simple undirected graphs to each finite label set. Heredity means closure under every injective induced restriction, including relabellings. Smallness requires heredity and a positive real constant c such that the number of labelled members on n vertices is at most n! c^n for every n ≥ 1; graphs are not counted up to isomorphism.
--
--   For a finite graph G, sets A and B of its vertices, and a vertex v, define the open-neighbourhood trace and its image family by
--
--   $$N_A(v)=\{u\in A:G.Adj(v,u)\},\qquad N_A(B)=\{N_A(v):v\in B\}.$$
--
--   B is A-diverse if these traces distinguish its vertices. It is minimally A-diverse if A is nonempty, B is A-diverse, and every nonempty proper U ⊂ A has fewer than (|B|/|A|)|U| traces. The quotient is real. A bipartition specifies disjoint A,B and only cross edges. A minimal pair with parameter C additionally requires nonempty parts, |B| ≥ C|A|, and the two strict trace bounds (M1) on proper subsets of A and (M2) on proper subsets of B.
--
--   The core is the induced graph on the actual subtype A ∪ B, and its automorphism count includes all automorphisms, without precolouring the parts. Extending such permutations by the identity outside the core is a notational convenience. Setwise preservation and pointwise fixation are separate predicates. These definitions supply the common graph interface for the goal and milestones. Fin n labels are shifted by one to match [n].
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), §§1–2.3, printed pp. 1–2, 7–9 and 11 (PDF pp. 2–3, 8–10 and 12)

import Mathlib

noncomputable section

namespace SmallClassesNeighbourhood.Linear

/-- Labelled finite graph classes. Induced restrictions include every relabelling. -/
def GraphClass := (n : ℕ) → Set (SimpleGraph (Fin n))

def IsHereditary (𝒞 : GraphClass) : Prop :=
  ∀ {m n : ℕ} (G : SimpleGraph (Fin n)), G ∈ 𝒞 n →
    ∀ f : Fin m ↪ Fin n, G.comap f ∈ 𝒞 m

def IsSmall (𝒞 : GraphClass) : Prop := IsHereditary 𝒞 ∧
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    (Nat.card {G : SimpleGraph (Fin n) // G ∈ 𝒞 n} : ℝ) ≤ (n.factorial : ℝ) * c ^ n

variable {V : Type} [Fintype V] [DecidableEq V]

def trace (G : SimpleGraph V) (A : Finset V) (v : V) : Finset V := by
  classical
  exact A.filter (G.Adj v)

def traces (G : SimpleGraph V) (A B : Finset V) : Finset (Finset V) := by
  classical
  exact B.image (trace G A)

def Diverse (G : SimpleGraph V) (A B : Finset V) : Prop :=
  Set.InjOn (trace G A) (↑B : Set V)

def MinimallyDiverse (G : SimpleGraph V) (A B : Finset V) : Prop :=
  A.Nonempty ∧ Diverse G A B ∧ ∀ U : Finset V, U.Nonempty → U ⊂ A →
    ((traces G U B).card : ℝ) < (B.card : ℝ) / (A.card : ℝ) * (U.card : ℝ)

/-- All edges of F are cross edges between the named disjoint parts. -/
def Bipartition (F : SimpleGraph V) (A B : Finset V) : Prop :=
  Disjoint A B ∧ ∀ x y : V, F.Adj x y →
    (x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A)

def MinimalPair (C : ℕ) (F : SimpleGraph V) (A B : Finset V) : Prop :=
  Bipartition F A B ∧ A.Nonempty ∧ B.Nonempty ∧ Diverse F A B ∧
  C * A.card ≤ B.card ∧
  (∀ U : Finset V, U.Nonempty → U ⊂ A → (traces F U B).card < C * U.card) ∧
  (∀ U : Finset V, U.Nonempty → U ⊂ B → (traces F U A).card < C * U.card)

/-- The actual vertex type is A ∪ B: ambient isolated vertices are excluded. -/
abbrev Core (F : SimpleGraph V) (A B : Finset V) := F.induce (↑(A ∪ B) : Set V)

abbrev CoreAut (F : SimpleGraph V) (A B : Finset V) := Core F A B ≃g Core F A B

def autCount (F : SimpleGraph V) (A B : Finset V) : ℕ := Nat.card (CoreAut F A B)

/-- Extend an automorphism by the identity outside the actual vertex set, only for notation. -/
def ambientPerm {F : SimpleGraph V} {A B : Finset V} (σ : CoreAut F A B) : Equiv.Perm V := by
  classical
  exact σ.toEquiv.subtypeCongr (Equiv.refl _)

def Preserves (σ : V → V) (S : Finset V) : Prop := ∀ x : V, σ x ∈ S ↔ x ∈ S

def Fixes (σ : V → V) (S : Finset V) : Prop := ∀ x ∈ S, σ x = x

end SmallClassesNeighbourhood.Linear


