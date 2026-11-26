-- Prove2me | Definitions.Def_BKAR_Differential
-- name    : BKAR_Differential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:19:49.788724+00:00
-- url     : https://prove2.me/theorems/c54e1d66-ba31-556a-bc43-a9fd3232c2d5
-- title:
--   Differential
-- statement:
--   Definitions and structural lemmas for Differential, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Theorems.Thm_BKAR_Edge_left_ne_right
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_empty_inSameComponent_iff

set_option autoImplicit false
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def activeEdges (F : Forest V) : Finset (Edge V) :=
  (Finset.univ : Finset (Edge V)).filter
    (fun e => ¬ F.inSameComponent e.left e.right)
theorem mem_activeEdges_iff (F : Forest V) {e : Edge V} :
    e ∈ F.activeEdges ↔ ¬ F.inSameComponent e.left e.right := by
  rw [activeEdges, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ e, h⟩⟩
theorem empty_activeEdges :
    (Forest.empty V).activeEdges = (Finset.univ : Finset (Edge V)) := by
  ext e
  rw [(Forest.empty V).mem_activeEdges_iff]
  constructor
  · intro _
    exact Finset.mem_univ e
  · intro _ hcomp
    exact e.left_ne_right (Forest.empty_inSameComponent_iff.mp hcomp)
noncomputable def emptyActiveEdge (e : Edge V) :
    {e // e ∈ (Forest.empty V).activeEdges} :=
  ⟨e, by
    rw [empty_activeEdges]
    exact Finset.mem_univ e⟩
noncomputable def activeDirection (F : Forest V) : Edge V → ℝ :=
  Finset.sum F.activeEdges edgeBasis
noncomputable def activeEdgePartialSum (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) : ℝ :=
  Finset.sum F.activeEdges fun e => partialDeriv e ρ (F.interpWithFill u t)
def ActiveEdgeDerivIdentityAt (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) : Prop :=
  deriv (fun s : ℝ => ρ (F.interpWithFill u s)) t =
    F.activeEdgePartialSum u ρ t
end Forest
end BKAR


