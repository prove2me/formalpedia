-- Prove2me | Definitions.Def_GalvinLib_Orientation
-- name    : GalvinLib_Orientation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:37:29.990504+00:00
-- url     : https://prove2.me/theorems/fcd84419-b802-4e9b-afdf-b0be5ce80820
-- title:
--   Orientation
-- statement:
--   Definitions and structural lemmas for Orientation, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean

module
public import Definitions.Def_GalvinLib_GaleShapley
public import Definitions.Def_GalvinLib_Kernel
public import Mathlib.Order.Interval.Finset.Fin
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Galvin
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
theorem exists_ends (c : G.Coloring (Fin 2)) (e : G.edgeSet) :
    ∃ a b : V, (e : Sym2 V) = s(a, b) ∧ c a = 0 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ x y =>
  have hne : c x ≠ c y := c.valid he
  by_cases hx : c x = 0
  · exact ⟨x, y, rfl, hx⟩
  · refine ⟨y, x, Sym2.eq_swap, ?_⟩
    revert hne hx
    generalize c x = i
    generalize c y = j
    revert i j
    decide
noncomputable def endA (c : G.Coloring (Fin 2)) (e : G.edgeSet) : V :=
  (exists_ends c e).choose
noncomputable def endB (c : G.Coloring (Fin 2)) (e : G.edgeSet) : V :=
  (exists_ends c e).choose_spec.choose
def arc (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (e f : G.edgeSet) : Prop :=
  (endA c e = endA c f ∧ φ f < φ e) ∨ (endB c e = endB c f ∧ φ e < φ f)
noncomputable def rankA (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (idx : V → ℕ) (m w : V) : ℕ :=
  open Classical in
  if h : ∃ e : G.edgeSet, endA c e = m ∧ endB c e = w then (φ h.choose : ℕ) else Δ + idx w
noncomputable def rankB (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (idx : V → ℕ) (w m : V) : ℕ :=
  open Classical in
  if h : ∃ e : G.edgeSet, endA c e = m ∧ endB c e = w then Δ - (φ h.choose : ℕ)
  else Δ + 1 + idx m
end Galvin


