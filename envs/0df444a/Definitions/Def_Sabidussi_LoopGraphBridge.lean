-- Prove2me | Definitions.Def_Sabidussi_LoopGraphBridge
-- name    : Sabidussi_LoopGraphBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:10:21.486561+00:00
-- url     : https://prove2.me/theorems/325829ed-deac-46c1-8cdd-5b3457eb3355
-- title:
--   Loop Graph Bridge
-- statement:
--   Definitions and structural lemmas for Loop Graph Bridge, from Upstream contributors (gexahedron/sabidussi-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Sabidussi compatibility conjecture for finite Eulerian loop multigraphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LoopGraphBridge.lean

import Definitions.Def_Sabidussi_LoopMultigraph
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_localDifference_one
import Theorems.Thm_Sabidussi_localDifference_zero
import Theorems.Thm_Sabidussi_tripleDifference_one
import Theorems.Thm_Sabidussi_tripleDifference_two
import Theorems.Thm_Sabidussi_tripleDifference_zero
attribute [local simp] Sabidussi.bracketRightHom_apply
attribute [local simp] Sabidussi.bracket_self
attribute [local simp] Sabidussi.localDifference_one
attribute [local simp] Sabidussi.localDifference_zero
attribute [local simp] Sabidussi.tripleDifference_one
attribute [local simp] Sabidussi.tripleDifference_two
attribute [local simp] Sabidussi.tripleDifference_zero


set_option autoImplicit true
namespace Sabidussi
namespace LoopMultigraph
open Sabidussi
open scoped BigOperators
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : LoopMultigraph V E}
def EulerTour.eulerWord (T : G.EulerTour) : Sabidussi.CyclicWord.Word (V := V) where
  n := T.n
  letter := T.vertexAt
namespace EulerTour
variable (T : G.EulerTour)
@[simp]
theorem eulerWord_letter (i : T.Pos) : T.eulerWord.letter i = T.vertexAt i := rfl
@[simp]
theorem eulerWord_prev (i : T.Pos) : T.eulerWord.prev i = T.prev i := rfl
def revFinTwoEquiv : Fin 2 ≃ Fin 2 :=
  Fin.rev_involutive.toPerm
def wordOccurrenceSideEquivHalfEdgesAt (v : V) :
    T.eulerWord.Occurrence v × Fin 2 ≃ G.halfEdgesAt v :=
  (Equiv.prodCongr (Equiv.refl _) revFinTwoEquiv).trans
    (T.occurrenceSideEquivHalfEdgesAt v)
theorem incidentColor_eq_halfEdgeColor
    (x : T.eulerWord.Pos → Color) {v : V}
    (os : T.eulerWord.Occurrence v × Fin 2) :
    T.eulerWord.incidentColor x os.1 os.2 =
      x (T.edge.symm ((T.wordOccurrenceSideEquivHalfEdgesAt v os).1.1)) := by
  rcases os with ⟨o, s⟩
  fin_cases s
  · change x (T.prev o.1) = x (T.edge.symm (T.edge (T.prev o.1)))
    simp
  · change x o.1 = x (T.edge.symm (T.edge o.1))
    exact (congrArg x (T.edge.symm_apply_apply o.1)).symm
def coloredOccurrenceSideEquivColoredHalfEdgesAt
    (C : T.eulerWord.Coloring) (v : V) (z : Color) :
    {os : T.eulerWord.Occurrence v × Fin 2 //
      T.eulerWord.incidentColor C.color os.1 os.2 = z} ≃
    {h : G.halfEdgesAt v // C.color (T.edge.symm h.1.1) = z} :=
  (T.wordOccurrenceSideEquivHalfEdgesAt v).subtypeEquiv fun os ↦ by
    rw [T.incidentColor_eq_halfEdgeColor C.color os]
theorem sum_support_edgeIncidence_eq_sum_halfEdgesAt
    (color : E → Color) (z : Color) (v : V) :
    (∑ e ∈ (Finset.univ.filter fun e ↦ color e = z), G.edgeIncidence v e) =
      ∑ h : G.halfEdgesAt v, if color h.1.1 = z then 1 else 0 := by
  change (∑ e ∈ (Finset.univ.filter fun e ↦ color e = z), G.edgeIncidence v e) =
    ∑ h : {h : HalfEdge E // G.vertex h = v}, if color h.1.1 = z then 1 else 0
  rw [← Finset.sum_subtype (Finset.univ.filter fun h : HalfEdge E ↦ G.vertex h = v)
    (by simp) (fun h : HalfEdge E ↦ if color h.1 = z then (1 : F₂) else 0)]
  rw [Finset.sum_filter]
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro e
  rw [Fin.sum_univ_two]
  by_cases he : color e = z <;> simp [edgeIncidence, vertex, he]
theorem isEvenEdgeSet_of_coloredHalfEdgesAt_even
    (color : E → Color)
    (heven : ∀ (v : V) (z : Color),
      Even (Fintype.card {h : G.halfEdgesAt v // color h.1.1 = z})) (z : Color) :
    G.IsEvenEdgeSet (Finset.univ.filter fun e ↦ color e = z) := by
  intro v
  rw [sum_support_edgeIncidence_eq_sum_halfEdgesAt color z v]
  rw [Finset.sum_boole]
  rw [← Fintype.card_subtype]
  exact ZMod.natCast_eq_zero_iff_even.mpr (heven v z)
noncomputable def compatibleFourColoringOfWordColoring
    (C : T.eulerWord.Coloring) : G.CompatibleFourColoring T where
  color := fun e ↦ C.color (T.edge.symm e)
  transition_ne := by
    intro i
    simpa using C.transition_ne i
  color_even := by
    apply isEvenEdgeSet_of_coloredHalfEdgesAt_even
    intro v z
    rw [← Fintype.card_congr (T.coloredOccurrenceSideEquivColoredHalfEdgesAt C v z)]
    exact C.color_even v z
end EulerTour
end LoopMultigraph
end Sabidussi


