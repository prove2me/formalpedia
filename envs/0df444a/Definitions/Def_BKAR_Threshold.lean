-- Prove2me | Definitions.Def_BKAR_Threshold
-- name    : BKAR_Threshold
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:17:12.357279+00:00
-- url     : https://prove2.me/theorems/145f8c6b-62ec-5972-aae9-9e84011b2002
-- title:
--   Threshold
-- statement:
--   Definitions and structural lemmas for Threshold, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Threshold.lean

import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_EdgePath_IsPath_mono
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_mono
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_IsAcyclicEdgeSet_mono
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil


set_option autoImplicit false
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
def thresholdEdges (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) :
    Finset (Edge V) :=
  F.edges.filter fun e => s ≤ F.paramValue u e
@[simp]
theorem mem_thresholdEdges (F : Forest V) (u : F.EdgeParam → ℝ)
    (s : ℝ) (e : Edge V) :
    e ∈ F.thresholdEdges u s ↔ e ∈ F.edges ∧ s ≤ F.paramValue u e := by
  simp [thresholdEdges]
def thresholdIndex (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) :
    ForestIndex V where
  edges := F.thresholdEdges u s
  acyclic := F.isAcyclicEdgeSet.mono (by
    intro e he
    exact (F.mem_thresholdEdges u s e).mp he |>.1)
def thresholdConnected (F : Forest V) (u : F.EdgeParam → ℝ)
    (s : ℝ) (i j : V) : Prop :=
  ∃ γ : List (Edge V),
    IsSimplePath F γ i j ∧ ∀ e ∈ γ, s ≤ F.paramValue u e
end
end Forest
end BKAR


