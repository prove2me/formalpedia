-- Prove2me | Definitions.Def_BKAR_ThresholdComponents
-- name    : BKAR_ThresholdComponents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:17:30.188627+00:00
-- url     : https://prove2.me/theorems/9b16f9aa-4e09-5a97-9032-7f7b6be03e97
-- title:
--   Threshold Components
-- statement:
--   Definitions and structural lemmas for Threshold Components, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdComponents.lean

import Mathlib.Order.Partition.Finpartition
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Threshold
import Theorems.Thm_BKAR_AcyclicEdgeSetData_inSameComponent_refl
import Theorems.Thm_BKAR_AcyclicEdgeSetData_inSameComponent_symm
import Theorems.Thm_BKAR_AcyclicEdgeSetData_inSameComponent_trans
import Theorems.Thm_BKAR_EdgePath_IsPath_mono
import Theorems.Thm_BKAR_EdgePath_IsPath_mono_of_forall_mem
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_mono
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_mono_of_forall_mem
import Theorems.Thm_BKAR_Forest_inSameComponent_trans
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathInF_isSimple
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_IsAcyclicEdgeSet_mono
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil


set_option autoImplicit false
namespace BKAR
open scoped BigOperators
namespace Finpartition
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
end
end Finpartition
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
def thresholdForest (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) :
    Forest V :=
  (Classical.choice (F.thresholdIndex u s).acyclic).toForest
@[simp]
theorem thresholdForest_edges (F : Forest V) (u : F.EdgeParam → ℝ)
    (s : ℝ) :
    (F.thresholdForest u s).edges = F.thresholdEdges u s :=
  rfl
theorem thresholdConnected_iff_thresholdForest_inSameComponent
    (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) (i j : V) :
    F.thresholdConnected u s i j ↔
      (F.thresholdForest u s).inSameComponent i j := by
  constructor
  · rintro ⟨γ, hγ, hall⟩
    refine Forest.inSameComponent_of_isSimplePath
      (F := F.thresholdForest u s) (γ := γ) ?_
    rw [IsSimplePath]
    rw [(F.thresholdForest u s).acyclic.isSimplePath_iff]
    have hγGraph : EdgePath.IsSimplePath F.edges γ i j :=
      F.acyclic.isSimplePath_iff.mp hγ
    have hγThreshold : EdgePath.IsSimplePath (F.thresholdEdges u s) γ i j :=
      hγGraph.mono_of_forall_mem fun e he =>
        (F.mem_thresholdEdges u s e).mpr
          ⟨hγGraph.edge_mem e he, hall e he⟩
    simpa using hγThreshold
  · intro hcomp
    let γ := (F.thresholdForest u s).pathInF i j hcomp
    have hγThresholdSimple :
        IsSimplePath (F.thresholdForest u s) γ i j :=
      (F.thresholdForest u s).pathInF_isSimple hcomp
    have hγThresholdGraph :
        EdgePath.IsSimplePath (F.thresholdEdges u s) γ i j := by
      rw [IsSimplePath] at hγThresholdSimple
      exact (F.thresholdForest u s).acyclic.isSimplePath_iff.mp
        hγThresholdSimple
    refine ⟨γ, ?_, ?_⟩
    · rw [IsSimplePath]
      rw [F.acyclic.isSimplePath_iff]
      exact hγThresholdGraph.mono fun e he =>
        (F.mem_thresholdEdges u s e).mp he |>.1
    · intro e he
      exact (F.mem_thresholdEdges u s e).mp
        (hγThresholdGraph.edge_mem e he) |>.2
theorem thresholdConnected_refl
    (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) (i : V) :
    F.thresholdConnected u s i i := by
  rw [F.thresholdConnected_iff_thresholdForest_inSameComponent u s]
  exact (F.thresholdForest u s).acyclic.inSameComponent_refl i
theorem thresholdConnected_symm
    (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ)
    {i j : V} (h : F.thresholdConnected u s i j) :
    F.thresholdConnected u s j i := by
  rw [F.thresholdConnected_iff_thresholdForest_inSameComponent u s] at h ⊢
  exact (F.thresholdForest u s).acyclic.inSameComponent_symm h
theorem thresholdConnected_trans
    (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ)
    {i j k : V} (hij : F.thresholdConnected u s i j)
    (hjk : F.thresholdConnected u s j k) :
    F.thresholdConnected u s i k := by
  rw [F.thresholdConnected_iff_thresholdForest_inSameComponent u s] at hij hjk ⊢
  exact (F.thresholdForest u s).inSameComponent_trans hij hjk
def thresholdSetoid (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) :
    Setoid V where
  r := F.thresholdConnected u s
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact F.thresholdConnected_refl u s i
    · intro i j hij
      exact F.thresholdConnected_symm u s hij
    · intro i j k hij hjk
      exact F.thresholdConnected_trans u s hij hjk
def thresholdPartition (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) :
    Finpartition (Finset.univ : Finset V) := by
  classical
  exact Finpartition.ofSetoid (F.thresholdSetoid u s)
def thresholdComponent (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ)
    (i : V) : Finset V :=
  (F.thresholdPartition u s).part i
end
end Forest
end BKAR


