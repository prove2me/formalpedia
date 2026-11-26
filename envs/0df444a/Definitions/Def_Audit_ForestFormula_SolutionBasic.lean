-- Prove2me | Definitions.Def_Audit_ForestFormula_SolutionBasic
-- name    : Audit_ForestFormula_SolutionBasic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:11:49.60518+00:00
-- url     : https://prove2.me/theorems/bda825f7-168d-5e3c-99c0-089426a16ce2
-- title:
--   Solution Basic
-- statement:
--   Definitions and structural lemmas for Solution Basic, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/Audit/ForestFormula/SolutionBasic.lean

import Mathlib
import Definitions.Def_BKAR
import Theorems.Thm_BKAR_ForestIndex_canonicalOrder_val
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_edgeParamFinEquivOfOrder_apply_val
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_mem_thresholdComponent
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_self_mem_thresholdComponent
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_mixedPartialList_cons
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
import Theorems.Thm_BKAR_mixedPartialList_nil
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_cons
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_nil
import Theorems.Thm_BKAR_orderedSimplexIntegral_cons
import Theorems.Thm_BKAR_orderedSimplexIntegral_nil
import Theorems.Thm_BKAR_orderedSimplexParams_cons
import Theorems.Thm_BKAR_orderedSimplexParams_nil
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegralAux_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegral_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegrand_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.derivativeOrder_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_cons
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_nil
attribute [local simp] BKAR.Forest.edgeParamFinEquivOfOrder_apply_val
attribute [local simp] BKAR.Forest.emptyActiveEdge_val
attribute [local simp] BKAR.Forest.mem_thresholdComponent
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.Forest.self_mem_thresholdComponent
attribute [local simp] BKAR.ForestIndex.canonicalOrder_val
attribute [local simp] BKAR.edgeBasis_self
attribute [local simp] BKAR.mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.orderedSimplexIntegralAux_cons
attribute [local simp] BKAR.orderedSimplexIntegralAux_nil
attribute [local simp] BKAR.orderedSimplexIntegral_cons
attribute [local simp] BKAR.orderedSimplexIntegral_nil
attribute [local simp] BKAR.orderedSimplexParams_cons
attribute [local simp] BKAR.orderedSimplexParams_nil
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same


set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev Edge (V : Type*) [DecidableEq V] : Type _ := {e : Sym2 V // ¬ e.IsDiag}
noncomputable instance : Fintype (Edge V) := Fintype.ofFinite _
def Edge.left  (e : Edge V) : V := e.val.out.1
def Edge.right (e : Edge V) : V := e.val.out.2
def edgeGraph (S : Finset (Edge V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {x : Sym2 V | ∃ e : Edge V, e ∈ S ∧ e.val = x}
structure ForestIndex (V : Type*) [Fintype V] [DecidableEq V] where
  edges : Finset (Edge V)
  acyclic : (edgeGraph edges).IsAcyclic
namespace ForestIndex
noncomputable instance instFintype : Fintype (ForestIndex V) := by
  classical
  letI : DecidablePred (fun S : Finset (Edge V) => (edgeGraph S).IsAcyclic) :=
    fun _ => Classical.propDecidable _
  let e : ForestIndex V ≃ {S : Finset (Edge V) // (edgeGraph S).IsAcyclic} :=
    { toFun := fun F => ⟨F.edges, F.acyclic⟩
      invFun := fun S => ⟨S.1, S.2⟩
      left_inv := by intro F; cases F; rfl
      right_inv := by intro S; cases S; rfl }
  exact Fintype.ofEquiv _ e.symm
end ForestIndex
def paramValue (J : ForestIndex V) (u : {e : Edge V // e ∈ J.edges} → ℝ) (e : Edge V) : ℝ :=
  if h : e ∈ J.edges then u ⟨e, h⟩ else 1
def thresholdGraph (J : ForestIndex V) (u : {e : Edge V // e ∈ J.edges} → ℝ) (s : ℝ) :
    SimpleGraph V :=
  SimpleGraph.fromEdgeSet {x : Sym2 V | ∃ e : Edge V, e ∈ J.edges ∧ e.val = x ∧ s ≤ paramValue J u e}
def standardInterp (J : ForestIndex V) (u : {e : Edge V // e ∈ J.edges} → ℝ) :
    Edge V → ℝ :=
  fun e => sSup {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ (thresholdGraph J u s).Reachable e.left e.right}
def updateCoord (x : Edge V → ℝ) (e : Edge V) (t : ℝ) : Edge V → ℝ := Function.update x e t
def partialDeriv (e : Edge V) (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) : ℝ :=
  deriv (fun t : ℝ => ρ (updateCoord x e t)) (x e)
def mixedPartialList : List (Edge V) → ((Edge V → ℝ) → ℝ) → (Edge V → ℝ) → ℝ
  | [], ρ => ρ
  | e :: es, ρ => partialDeriv e (mixedPartialList es ρ)
def mixedPartial (J : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) : (Edge V → ℝ) → ℝ :=
  mixedPartialList J.edges.toList ρ
def unitCube (J : ForestIndex V) : Set ({e : Edge V // e ∈ J.edges} → ℝ) :=
  Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1
def cubeContribution (J : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  ∫ u in unitCube J, mixedPartial J ρ (standardInterp J u)
def ContDiffHyp (ρ : (Edge V → ℝ) → ℝ) : Prop := ContDiff ℝ (∞ : WithTop ℕ∞) ρ
theorem acyclic_bridge (S : Finset (Edge V)) :
    (edgeGraph S).IsAcyclic ↔ BKAR.IsAcyclicEdgeSet S := by
  constructor
  · intro h
    -- `hG : (edgeSetGraph S).IsAcyclic`; build an `AcyclicEdgeSetData S`
    -- (the constructor from `isAcyclicEdgeSet_insert_of_not_inSameComponent`).
    have hG : (BKAR.EdgePath.edgeSetGraph S).IsAcyclic := h
    refine ⟨{
      inSameComponent := fun i j =>
        ∃ γ : List (Edge V), BKAR.EdgePath.IsSimplePath S γ i j
      isSimplePath := fun γ i j =>
        BKAR.EdgePath.IsSimplePath S γ i j
      pathIn := fun _ _ h => Classical.choose h
      pathIn_isSimple := ?_
      isSimplePath_iff := ?_
      sameComponent_of_simplePath := ?_
      path_unique := ?_
      path_edges_mem := ?_
      edge_isSimplePath := ?_ }⟩
    · intro i j h
      exact Classical.choose_spec h
    · intro i j γ
      rfl
    · intro i j γ hγ
      exact ⟨γ, hγ⟩
    · intro i j γ₁ γ₂ hγ₁ hγ₂
      exact BKAR.EdgePath.IsSimplePath.unique_of_isAcyclic hG hγ₁ hγ₂
    · intro i j γ hγ e' he'
      exact hγ.edge_mem e' he'
    · intro e' he'
      exact
        ⟨BKAR.EdgePath.IsPath.cons he' e'.between_left_right
          (BKAR.EdgePath.IsPath.nil e'.right), by simp⟩
  · rintro ⟨data⟩
    exact data.edgeSetGraph_isAcyclic
def indexEquiv : ForestIndex V ≃ BKAR.ForestIndex V where
  toFun J := ⟨J.edges, (acyclic_bridge J.edges).mp J.acyclic⟩
  invFun I := ⟨I.edges, (acyclic_bridge I.edges).mpr I.acyclic⟩
  left_inv := by intro J; cases J; rfl
  right_inv := by intro I; cases I; rfl
end BKARMirror


