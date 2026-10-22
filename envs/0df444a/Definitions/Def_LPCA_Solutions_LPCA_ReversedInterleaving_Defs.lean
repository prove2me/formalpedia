-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ReversedInterleaving_Defs
-- name    : LPCA_Solutions_LPCA_ReversedInterleaving_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:21:45.230089+00:00
-- url     : https://prove2.me/theorems/ea2bd7af-6773-4ede-ba9b-bfb403f687f2
-- title:
--   Interleavings of reversed-real functors in an arbitrary category
-- statement:
--   For reversed real-indexed functors with values in an arbitrary category, an epsilon interleaving consists of maps from t+epsilon to t, both naturality squares, and both double-shift equalities with the existing structure maps. The shift is nonnegative. Functors preserve this data with the same shift; no vector-space, finite-dimensionality or interval-decomposition hypothesis is used.
--
--   The included constructions and necessary compatibility results are:
--
--   - The actual structure map of a reversed real-indexed functor.
--   - An epsilon interleaving of reversed real-indexed persistence functors. Shifted objects map from t+epsilon to t; both naturality squares and both double-shift composites are required as equalities of actual morphisms.
--   - Interleavings are preserved by a functor, with the same shift and the actual images of all component and structure maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_ReversedInterleaving.lean, selected declarations in lines 12–82; source SHA-256 2202a18972537b3c6cce88ca1bbce6dd3cc66ed9c38be116293eaedfa96989f7; source certificate Sapelo2 job 49172236.

import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u v

theorem twiceShift_le (t ε : ℝ) (hε : 0 ≤ ε) : t ≤ (t + ε) + ε :=
  (le_add_of_nonneg_right hε).trans (le_add_of_nonneg_right hε)

/-- The actual structure map of a reversed real-indexed functor. -/
def reversedTransition {C : Type u} [Category.{v} C]
    (F : OrderDual ℝ ⥤ C) {s t : ℝ} (h : s ≤ t) :
    F.obj (OrderDual.toDual t) ⟶ F.obj (OrderDual.toDual s) :=
  F.map (homOfLE (show OrderDual.toDual t ≤ OrderDual.toDual s from h))

/-- An epsilon interleaving of reversed real-indexed persistence functors.
Shifted objects map from t+epsilon to t; both naturality squares and both
double-shift composites are required as equalities of actual morphisms. -/
structure ReversedInterleaving {C : Type u} [Category.{v} C]
    (F G : OrderDual ℝ ⥤ C) (ε : ℝ) where
  nonneg : 0 ≤ ε
  forward : ∀ t : ℝ, F.obj (OrderDual.toDual (t + ε)) ⟶ G.obj (OrderDual.toDual t)
  backward : ∀ t : ℝ, G.obj (OrderDual.toDual (t + ε)) ⟶ F.obj (OrderDual.toDual t)
  forward_naturality : ∀ (s t : ℝ) (h : s ≤ t),
    reversedTransition F (s := s + ε) (t := t + ε) (add_le_add h (le_refl ε)) ≫ forward s =
      forward t ≫ reversedTransition G h
  backward_naturality : ∀ (s t : ℝ) (h : s ≤ t),
    reversedTransition G (s := s + ε) (t := t + ε) (add_le_add h (le_refl ε)) ≫ backward s =
      backward t ≫ reversedTransition F h
  left_triangle : ∀ t : ℝ, forward (t + ε) ≫ backward t =
    reversedTransition F (twiceShift_le t ε nonneg)
  right_triangle : ∀ t : ℝ, backward (t + ε) ≫ forward t =
    reversedTransition G (twiceShift_le t ε nonneg)

namespace ReversedInterleaving

variable {C : Type u} [Category.{v} C]
variable {F G : OrderDual ℝ ⥤ C} {ε : ℝ}



/-- Interleavings are preserved by a functor, with the same shift and
the actual images of all component and structure maps. -/
def map {D : Type*} [Category* D] (α : ReversedInterleaving F G ε) (H : C ⥤ D) :
    ReversedInterleaving (F ⋙ H) (G ⋙ H) ε where
  nonneg := α.nonneg
  forward t := H.map (α.forward t)
  backward t := H.map (α.backward t)
  forward_naturality s t h := by
    change H.map (reversedTransition F (s := s + ε) (t := t + ε)
      (add_le_add h (le_refl ε))) ≫ H.map (α.forward s) =
        H.map (α.forward t) ≫ H.map (reversedTransition G h)
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg (fun f => H.map f) (α.forward_naturality s t h)
  backward_naturality s t h := by
    change H.map (reversedTransition G (s := s + ε) (t := t + ε)
      (add_le_add h (le_refl ε))) ≫ H.map (α.backward s) =
        H.map (α.backward t) ≫ H.map (reversedTransition F h)
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg (fun f => H.map f) (α.backward_naturality s t h)
  left_triangle t := by
    change H.map (α.forward (t + ε)) ≫ H.map (α.backward t) =
      H.map (reversedTransition F (twiceShift_le t ε α.nonneg))
    rw [← H.map_comp]
    exact congrArg (fun f => H.map f) (α.left_triangle t)
  right_triangle t := by
    change H.map (α.backward (t + ε)) ≫ H.map (α.forward t) =
      H.map (reversedTransition G (twiceShift_le t ε α.nonneg))
    rw [← H.map_comp]
    exact congrArg (fun f => H.map f) (α.right_triangle t)

end ReversedInterleaving

end LPCA


