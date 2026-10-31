-- Prove2me | Definitions.Def_BulteauTranspositions_NPHard_ThreeDT
-- name    : BulteauTranspositions_NPHard_ThreeDT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:52:03.260999+00:00
-- url     : https://prove2.me/theorems/e512abb7-587c-4d68-8d6e-da0e677a7728
-- title:
--   3DT instances, deletion steps, collapsibility and equivalence
-- statement:
--   A 3DT-instance has a positive span n, a list of oriented triples partitioning a finite alphabet, and distinct positions from 1 through n for its symbols. Natural numbers label the symbols; the flattened list of triple entries must have no duplicates. Triple list order is representational. Vacant positions remain dots in the same span. The induced order compares occupied positions, and consecutiveness excludes another occupied symbol between them. A triple is well ordered when its cyclic orientation agrees with increasing positions, allowing abc, bca and cab. A step deletes this triple and applies the inverse of its block transposition to the remaining positions. Collapsibility is finite reachability of an empty triple list, including zero steps. Equivalence to a permutation requires π(0)=0, adjacency at every vacant position, and the cyclic predecessor equations at all occupied positions. It asserts neither that every instance has an equivalent permutation nor that any instance collapses.
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, definitions and constructions, printed/PDF pp. 4–10; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_Sorting

namespace BulteauTranspositions.NPHard

abbrev Triple := ℕ × ℕ × ℕ

def Triple.symbols (t : Triple) : List ℕ := [t.1, t.2.1, t.2.2]

/-- Finite symbol names are natural numbers; the list order of triples has no mathematical role. -/
structure Instance where
  span : ℕ
  triples : List Triple
  pos : ℕ → ℕ

def Instance.symbols (I : Instance) : List ℕ := I.triples.flatMap Triple.symbols

def Instance.WF (I : Instance) : Prop :=
  0 < I.span ∧ I.symbols.Nodup ∧
  (∀ a ∈ I.symbols, 1 ≤ I.pos a ∧ I.pos a ≤ I.span) ∧
  Set.InjOn I.pos {a | a ∈ I.symbols}

def Instance.domain (I : Instance) : Finset ℕ := (I.symbols.map I.pos).toFinset

def Instance.Before (I : Instance) (a b : ℕ) : Prop := I.pos a < I.pos b

def Instance.Consecutive (I : Instance) (a b : ℕ) : Prop :=
  I.Before a b ∧ ¬ ∃ c ∈ I.symbols, I.Before a c ∧ I.Before c b

def tripleCut (I : Instance) (t : Triple) : Cut :=
  let a := I.pos t.1
  let b := I.pos t.2.1
  let c := I.pos t.2.2
  if a ≤ b ∧ a ≤ c then ⟨a,b,c⟩ else if b ≤ c then ⟨b,c,a⟩ else ⟨c,a,b⟩

def WellOrdered (I : Instance) (t : Triple) : Prop :=
  t ∈ I.triples ∧ (tripleCut I t).Legal I.span

def Step (I : Instance) (t : Triple) (J : Instance) : Prop :=
  I.WF ∧ WellOrdered I t ∧ J.span = I.span ∧ J.triples = I.triples.erase t ∧
  (∀ a ∈ J.symbols, J.pos a = (tripleCut I t).inv.tau (I.pos a))

def Collapsible (I : Instance) : Prop :=
  ∃ J, Relation.ReflTransGen (fun U V => ∃ t, Step U t V) I J ∧ J.triples = []

/-- Each equation is the predecessor version of the cyclic successor rule, including gaps. -/
def Equivalent (I : Instance) (p : ℕ → ℕ) : Prop :=
  p 0 = 0 ∧
  (∀ v ∈ Finset.Icc 1 I.span, v ∉ I.domain → p v = p (v - 1) + 1) ∧
  ∀ t ∈ I.triples,
    p (I.pos t.2.1) = p (I.pos t.1 - 1) + 1 ∧
    p (I.pos t.2.2) = p (I.pos t.2.1 - 1) + 1 ∧
    p (I.pos t.1) = p (I.pos t.2.2 - 1) + 1

end BulteauTranspositions.NPHard


