-- Prove2me | Definitions.Def_LeanPool_Vizing_Basic
-- name    : LeanPool_Vizing_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:12.055645+00:00
-- url     : https://prove2.me/theorems/887eb3e5-66e4-43bf-b7d4-ebc99b00f81f
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
set_option autoImplicit true
@[expose] public section
@[expose] public section
section
open SimpleGraph Finset
namespace LeanPool.Vizing
variable {V : Type*} [DecidableEq V] {C : Type*}
structure PEC (G : SimpleGraph V) (C : Type*) where
  /-- The colour of the edge `u v`, if it is coloured. -/
  col : V → V → Option C
  col_symm : ∀ u v, col u v = col v u
  col_adj : ∀ {u v γ}, col u v = some γ → G.Adj u v
  col_proper : ∀ {u v w γ}, col u v = some γ → col u w = some γ → v = w
namespace PEC
variable {G : SimpleGraph V}
def IsFree (c : PEC G C) (v : V) (γ : C) : Prop := ∀ u, c.col v u ≠ some γ
def Extends (c c' : PEC G C) : Prop := ∀ u v, c.col u v ≠ none → c'.col u v ≠ none
def updFun (f : V → V → Option C) (x y : V) (o : Option C) : V → V → Option C :=
  fun u v => if (u = x ∧ v = y) ∨ (u = y ∧ v = x) then o else f u v
def setEdge (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) : PEC G C where
  col := updFun c.col x y (some γ)
  col_symm := by
    intro u v
    unfold updFun
    by_cases h : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
    · rw [if_pos h, if_pos (by tauto)]
    · rw [if_neg h, if_neg (by tauto)]
      exact c.col_symm u v
  col_adj := by
    intro u v δ h
    unfold updFun at h
    by_cases hc : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
    · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj
      · exact hadj.symm
    · rw [if_neg hc] at h
      exact c.col_adj h
  col_proper := by
    have key : ∀ u v δ, updFun c.col x y (some γ) u v = some δ →
        ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) ∨ c.col u v = some δ := by
      intro u v δ h
      unfold updFun at h
      by_cases hc : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
      · exact Or.inl hc
      · rw [if_neg hc] at h
        exact Or.inr h
    have hcol : ∀ u v δ, updFun c.col x y (some γ) u v = some δ →
        (((u = x ∧ v = y) ∨ (u = y ∧ v = x)) → δ = γ) := by
      intro u v δ h hc
      unfold updFun at h
      rw [if_pos hc] at h
      exact (Option.some_injective _ h).symm
    intro u v w δ h1 h2
    rcases key u v δ h1 with hc1 | hc1 <;> rcases key u w δ h2 with hc2 | hc2
    · rcases hc1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hc2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        subst_vars <;> rfl
    · have hd1 := hcol u v δ h1 hc1
      subst hd1
      rcases hc1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hc2 (hx w)
      · exact absurd hc2 (hy w)
    · have hd2 := hcol u w δ h2 hc2
      subst hd2
      rcases hc2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hc1 (hx v)
      · exact absurd hc1 (hy v)
    · exact c.col_proper hc1 hc2
end PEC
end LeanPool.Vizing
end


