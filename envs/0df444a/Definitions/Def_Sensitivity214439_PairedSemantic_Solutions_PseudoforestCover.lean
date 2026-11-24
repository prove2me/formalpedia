-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PseudoforestCover
-- name    : Sensitivity214439_PairedSemantic_Solutions_PseudoforestCover
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:46:10.372313+00:00
-- url     : https://prove2.me/theorems/840d4b48-092e-45fc-9ac9-b0c50c0d8ecb
-- title:
--   Directed neighborhoods, sinks, and weighted three-color covers
-- statement:
--   For a relation restricted to a finite set, define outgoing, incoming, and undirected neighbor sets, and define a sink to have no outgoing neighbor. A weighted three-color cover assigns each sink two colors and every other vertex one, with disjoint color palettes along every directed edge.
--
--   The supporting extension operations remove a vertex with no incoming edge and restore it with a compatible palette. Removing such a source preserves sink status of the remaining vertices, which makes the induction retain the exact population-plus-sinks weight.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/PseudoforestCover.lean lines 22–160; SHA256 e5f8acc9d97d8c67914f3708144ec7d81a98e150401cacf5ad609edb8b64f010; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Tauto

namespace SensitivityPseudoforest
end SensitivityPseudoforest



/-!
Three independent palettes for a finite orientation of outdegree at most one.
Sinks receive two colors, all other vertices one. This directly gives the
population-plus-sinks inequality without classifying connected components.
-/

namespace SensitivityPseudoforest

noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false

variable {V : Type}

def outgoing (R : V → V → Prop) (s : Finset V) (v : V) : Finset V := s.filter (R v)
def incoming (R : V → V → Prop) (s : Finset V) (v : V) : Finset V := s.filter (fun w => R w v)
def neighbors (R : V → V → Prop) (s : Finset V) (v : V) : Finset V :=
  s.filter (fun w => R v w ∨ R w v)
def IsSink (R : V → V → Prop) (s : Finset V) (v : V) : Prop := ∀ w ∈ s, ¬ R v w

structure WeightedCover (R : V → V → Prop) (s : Finset V) where
  colors : V → Finset (Fin 3)
  size : ∀ v ∈ s, (colors v).card = if IsSink R s v then 2 else 1
  proper : ∀ v ∈ s, ∀ w ∈ s, R v w → Disjoint (colors v) (colors w)













theorem sink_erase_source {R : V → V → Prop} {s : Finset V} {v : V}
    (hsource : ∀ w ∈ s, ¬ R w v) {w : V} (hw : w ∈ s) :
    IsSink R (s.erase v) w ↔ IsSink R s w := by
  constructor
  · intro h a ha hra
    by_cases hav : a = v
    · exact hsource w hw (hav ▸ hra)
    · exact h a (Finset.mem_erase.mpr ⟨hav, ha⟩) hra
  · intro h a ha
    exact h a (Finset.mem_of_mem_erase ha)

def extend_source_cover {R : V → V → Prop} {s : Finset V} {v : V}
    (hv : v ∈ s) (hsource : ∀ w ∈ s, ¬ R w v)
    (cover : WeightedCover R (s.erase v)) (palette : Finset (Fin 3))
    (hsize : palette.card = if IsSink R s v then 2 else 1)
    (hproper : ∀ w ∈ s.erase v, R v w → Disjoint palette (cover.colors w)) :
    WeightedCover R s where
  colors := Function.update cover.colors v palette
  size := by
    intro w hw
    by_cases hwv : w = v
    · subst w
      rw [Function.update_self]
      exact hsize
    · rw [Function.update_of_ne hwv,
        cover.size w (Finset.mem_erase.mpr ⟨hwv, hw⟩), sink_erase_source hsource hw]
  proper := by
    intro a ha b hb hab
    have hbne : b ≠ v := by intro h; exact hsource a ha (h ▸ hab)
    by_cases haeq : a = v
    · subst a
      rw [Function.update_self, Function.update_of_ne hbne]
      exact hproper b (Finset.mem_erase.mpr ⟨hbne, hb⟩) hab
    · rw [Function.update_of_ne haeq, Function.update_of_ne hbne]
      exact cover.proper a (Finset.mem_erase.mpr ⟨haeq, ha⟩)
        b (Finset.mem_erase.mpr ⟨hbne, hb⟩) hab








end
end SensitivityPseudoforest


