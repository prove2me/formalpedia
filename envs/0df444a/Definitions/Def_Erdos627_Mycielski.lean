-- Prove2me | Definitions.Def_Erdos627_Mycielski
-- name    : Erdos627_Mycielski
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:57:14.445592+00:00
-- url     : https://prove2.me/theorems/33f303da-1987-55f4-ac7f-3c34dbde0532
-- title:
--   Mycielski
-- statement:
--   Definitions and structural lemmas for Mycielski, from alexander (AItoBit/erdos-627-palomar; proof developed for google-deepmind/formal-conjectures PR 7259 under Apache-2.0; see pinned LICENSE and README.md)'s pinned Erdos Problem 627: Tutte-Zykov theorem via Mycielski construction development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.SplitIfs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SimpleGraph
variable {V : Type*}
def mycielskiAdj (G : SimpleGraph V) : Option (V ⊕ V) → Option (V ⊕ V) → Prop
  | none, some (.inr _) => True
  | some (.inr _), none => True
  | some (.inl v), some (.inl w) => G.Adj v w
  | some (.inl v), some (.inr w) => G.Adj v w
  | some (.inr v), some (.inl w) => G.Adj v w
  | _, _ => False
def mycielski (G : SimpleGraph V) : SimpleGraph (Option (V ⊕ V)) where
  Adj := mycielskiAdj G
  symm := ⟨by
    rintro (_ | (_ | _)) (_ | (_ | _)) <;> simp [mycielskiAdj, G.adj_comm]⟩
  loopless := ⟨by
    rintro (_ | (_ | _)) <;> simp [mycielskiAdj]⟩
@[simp] theorem mycielski_adj (G : SimpleGraph V) (v w : Option (V ⊕ V)) :
    G.mycielski.Adj v w ↔ mycielskiAdj G v w := Iff.rfl
variable {G : SimpleGraph V} {α : Type*} {k : ℕ}
def Coloring.mycielski (C : G.Coloring α) : G.mycielski.Coloring (Option α) :=
  Coloring.mk
    (fun
      | none => none
      | some (.inl v) => some (C v)
      | some (.inr v) => some (C v))
    (by
      rintro (_ | (_ | v)) (_ | (_ | w)) h <;>
        simp_all [mycielskiAdj]
      all_goals exact C.valid h)
theorem Colorable.mycielski (h : G.Colorable k) : G.mycielski.Colorable (k + 1) := by
  simpa using h.some.mycielski.colorable
noncomputable def Coloring.ofMycielski (C : G.mycielski.Coloring α) : G.Coloring α := by
  classical
  refine Coloring.mk (fun v => if C (some (.inl v)) = C none
    then C (some (.inr v)) else C (some (.inl v))) ?_
  intro v w h
  have hoo : C (some (.inl v)) ≠ C (some (.inl w)) := C.valid h
  have hos : C (some (.inl v)) ≠ C (some (.inr w)) := C.valid h
  have hso : C (some (.inr v)) ≠ C (some (.inl w)) := C.valid h
  split_ifs with hv hw
  · exact False.elim (hoo (hv.trans hw.symm))
  · exact hso
  · exact hos
  · exact hoo
theorem CliqueFree.mycielski {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    G.mycielski.CliqueFree 3 := by
  classical
  have htri (a b c : V) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
      False := hG {a, b, c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;>
    rcases c with _ | (_ | _) <;> simp_all only [mycielski_adj, mycielskiAdj]
  all_goals exact htri _ _ _ hab hac hbc
variable {W : Type*}
end SimpleGraph


