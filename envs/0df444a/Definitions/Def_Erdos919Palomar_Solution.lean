-- Prove2me | Definitions.Def_Erdos919Palomar_Solution
-- name    : Erdos919Palomar_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T18:08:20.686984+00:00
-- url     : https://prove2.me/theorems/3617ec68-05bc-45b6-ba71-b5ff4edf833b
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from mnn31 (mnn31/erdos-919-palomar; see pinned Apache-2.0 LICENSE and README.md)'s pinned Reductions for Erdos Problem 919 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean

module
public import Mathlib
set_option autoImplicit false
@[expose] public section
@[expose] public section
universe u
open Cardinal Ordinal Set SimpleGraph
noncomputable def SimpleGraph.chromaticCardinal {V : Type u} (G : SimpleGraph V) : Cardinal :=
  sInf {κ : Cardinal | ∃ (C : Type u) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}
namespace Erdos919
noncomputable section
def ColorableOn {V : Type*} (G : SimpleGraph V) (X : Set V) (α : Type*) : Prop :=
  ∃ c : V → α, ∀ x ∈ X, ∀ y ∈ X, G.Adj x y → c x ≠ c y
theorem ColorableOn.comap {A B : Type*} {G : SimpleGraph B} {Y : Set A} {α : Type*} (f : A → B)
    (h : ColorableOn G (f '' Y) α) : ColorableOn (G.comap f) Y α := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c ∘ f, fun a ha b hb hab => hc _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab⟩
section Blowup
variable {I : Type*} [LinearOrder I]
def blowup (H : SimpleGraph I) : SimpleGraph (I × I) where
  Adj p q := (p.1 < q.1 ∧ H.Adj p.1 q.1 ∧ q.1 ≤ p.2) ∨ (q.1 < p.1 ∧ H.Adj q.1 p.1 ∧ p.1 ≤ q.2)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun p h => by rcases h with h | h <;> exact lt_irrefl _ h.1⟩
theorem blowup_adj {H : SimpleGraph I} {p q : I × I} : (blowup H).Adj p q ↔
    ((p.1 < q.1 ∧ H.Adj p.1 q.1 ∧ q.1 ≤ p.2) ∨ (q.1 < p.1 ∧ H.Adj q.1 p.1 ∧ p.1 ≤ q.2)) :=
  Iff.rfl
theorem blowup_adj_fst {H : SimpleGraph I} {p q : I × I} (h : (blowup H).Adj p q) :
    H.Adj p.1 q.1 := by
  rcases blowup_adj.1 h with h | h
  · exact h.2.1
  · exact h.2.1.symm
def blowupColoring {H : SimpleGraph I} {α : Type*} (c : H.Coloring α) :
    (blowup H).Coloring α :=
  Coloring.mk (fun p => c p.1) (fun h => c.valid (blowup_adj_fst h))
end Blowup
section Tensor
def tensorTop {V : Type*} (H : SimpleGraph V) (T : Type*) : SimpleGraph (V × T) where
  Adj p q := H.Adj p.1 q.1 ∧ p.2 ≠ q.2
  symm := ⟨fun _ _ h => ⟨(And.left h).symm, (And.right h).symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩
theorem tensorTop_adj {V T : Type*} {H : SimpleGraph V} {p q : V × T} :
    (tensorTop H T).Adj p q ↔ (H.Adj p.1 q.1 ∧ p.2 ≠ q.2) := Iff.rfl
def tensorTopColoringT {V : Type*} (H : SimpleGraph V) (T : Type*) :
    (tensorTop H T).Coloring T :=
  Coloring.mk (fun p => p.2) (fun h => (tensorTop_adj.1 h).2)
end Tensor
section Shift
variable (I : Type*) [LinearOrder I]
def shift : SimpleGraph {p : I × I // p.1 < p.2} where
  Adj p q := p.1.2 = q.1.1 ∨ q.1.2 = p.1.1
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun p h => by rcases h with h | h <;> exact (ne_of_lt p.2) h.symm⟩
variable {I}
noncomputable def diffColor {T : Type*} [LinearOrder T] [WellFoundedLT T] [Inhabited T]
    (x y : T → Bool) : T × Bool := by
  classical
  exact if h : ∃ t, x t ≠ y t then
    (WellFounded.min wellFounded_lt {t | x t ≠ y t} h,
      x (WellFounded.min wellFounded_lt {t | x t ≠ y t} h))
  else (default, false)
end Shift
section Transport
def SmallCardCC {V : Type u} (H : SimpleGraph V) : Prop :=
  ∀ X : Set V, #X ≤ ℵ₁ → ColorableOn H X ℕ
def ChiAleph2 {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ α : Type u, #α ≤ ℵ₁ → IsEmpty (G.Coloring α)
def ChiAleph1 {V : Type u} (G : SimpleGraph V) : Prop :=
  (∃ α : Type u, #α ≤ ℵ₁ ∧ Nonempty (G.Coloring α)) ∧ IsEmpty (G.Coloring ℕ)
def coloringComap {V V' α : Type*} (f : V → V') {G : SimpleGraph V'} (c : G.Coloring α) :
    (G.comap f).Coloring α :=
  Coloring.mk (c ∘ f) (fun h => c.valid h)
def coloringOfComap {V V' α : Type*} (e : V ≃ V') {G : SimpleGraph V'}
    (c : (G.comap e).Coloring α) : G.Coloring α :=
  Coloring.mk (c ∘ e.symm) (fun {x y} h => c.valid (by simpa [comap_adj] using h))
def coloringULift {V α : Type*} {G : SimpleGraph V} (c : G.Coloring α) :
    G.Coloring (ULift.{u} α) :=
  Coloring.mk (fun v => ULift.up (c v)) (fun h e => c.valid h (congrArg ULift.down e))
def coloringDown {V α : Type*} {G : SimpleGraph V} (c : G.Coloring (ULift.{u} α)) :
    G.Coloring α :=
  Coloring.mk (fun v => (c v).down) (fun h e => c.valid h (ULift.ext _ _ e))
end Transport
section Omega2
abbrev W : Type u := (ℵ_ 2 : Cardinal.{u}).ord.ToType
theorem typeLT_lex : typeLT (W.{u} ×ₗ W.{u}) = ω_ 2 ^ 2 := by
  have : typeLT (W.{u} ×ₗ W.{u}) = (typeLT W.{u}) * (typeLT W.{u}) :=
    type_prod_lex (· < ·) (· < ·)
  rw [this, type_toType, ord_aleph, sq]
end Omega2
def SmallTypeCC (G : SimpleGraph (W.{u} ×ₗ W.{u})) : Prop :=
  ∀ X : Set (W.{u} ×ₗ W.{u}), typeLT X < ω_ 2 ^ 2 → ColorableOn G X ℕ
def bigGraph (H : SimpleGraph W.{u}) : SimpleGraph (W.{u} ×ₗ W.{u}) := (blowup H).comap ofLex
def bigGraphColoring {H : SimpleGraph W.{u}} {α : Type u} (c : H.Coloring α) :
    (bigGraph H).Coloring α :=
  coloringComap ofLex (blowupColoring c)
abbrev T1 : Type u := (ℵ₁ : Cardinal.{u}).ord.ToType
section Chromatic
end Chromatic
section Vertices
abbrev V9 : Type u := (ω_ 2 ^ 2 : Ordinal.{u}).ToType
theorem typeLT_V9 : typeLT V9.{u} = typeLT (W.{u} ×ₗ W.{u}) := by
  rw [type_toType, typeLT_lex]
def isoV9 : V9.{u} ≃o W.{u} ×ₗ W.{u} :=
  OrderIso.ofRelIsoLT (Classical.choice (type_eq.1 typeLT_V9))
def Q (κ : Cardinal.{u}) : Prop :=
  ∃ G : SimpleGraph V9.{u}, G.chromaticCardinal = κ ∧
    ∀ X : Set V9.{u}, typeLT X < ω_ 2 ^ 2 → (G.induce X).chromaticCardinal ≤ ℵ₀
end Vertices
section Size
section
universe v
end
end Size
end
end Erdos919


