-- Prove2me | Definitions.Def_CSL_Circuit_NetworkModel_Adjacency
-- name    : CSL_Circuit_NetworkModel_Adjacency
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:13:29.562648+00:00
-- url     : https://prove2.me/theorems/51382611-cbee-44f2-a0c2-7f7c230aede2
-- title:
--   Coded sorting library: Circuit / NetworkModel / Adjacency
-- statement:
--   Module `CodedSorting.Circuit.NetworkModel.Adjacency` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Transfer a relation on the chronological active visits to every physical
--   wire edge, including the private pass subdivisions.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.NetworkModel.Adjacency

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Labels_Framework_StageLabels
import Mathlib.Data.List.Chain

/-! Transfer a relation on the chronological active visits to every physical
wire edge, including the private pass subdivisions. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CSL.Construction.MachineNetworkAdjacency

open CSL.TensorLabels CSL.StageLabels CSL.ProgramNetwork
open CSL.CircuitProgram

noncomputable section

variable {d : ℕ} {G Reg : Type*} [DecidableEq Reg]

theorem stageLabels_chain (R : Label d → Label d → Prop) (hrefl : ∀ P, R P P)
    (active : G → Bool) (label : G → Label d) (gs : List G) (P T : Label d)
    (h : List.Chain R P ((gs.filter active).map label ++ [T])) :
    List.Chain R P (stageLabels active label P gs ++ [T]) := by
  induction gs generalizing P with
  | nil => exact h
  | cons g gs ih =>
    by_cases hg : active g = true
    · have h' : List.IsChain R (P :: label g :: ((gs.filter active).map label ++ [T])) := by
        have h0 : List.IsChain R (P :: ((g :: gs).filter active).map label ++ [T]) := h
        simpa [List.filter_cons, hg] using h0
      have hh := List.isChain_cons_cons.mp h'
      have hrest := ih (label g) hh.2
      change List.IsChain R (P :: (if active g then label g else P) ::
        (stageLabels active label (if active g then label g else P) gs ++ [T]))
      rw [if_pos hg]
      exact List.isChain_cons_cons.mpr ⟨hh.1, hrest⟩
    · have hf : active g = false := Bool.eq_false_iff.mpr hg
      have hh : List.Chain R P ((gs.filter active).map label ++ [T]) := by
        have h0 : List.IsChain R (P :: ((g :: gs).filter active).map label ++ [T]) := h
        have h1 : List.IsChain R (P :: ((gs.filter active).map label ++ [T])) := by
          simpa [List.filter_cons, hf] using h0
        exact h1
      have hrest := ih P hh
      change List.IsChain R (P :: (if active g then label g else P) ::
        (stageLabels active label (if active g then label g else P) gs ++ [T]))
      rw [if_neg hg]
      exact List.isChain_cons_cons.mpr ⟨hrefl P, hrest⟩

theorem physical_edge_relation
    (R : Label d → Label d → Prop) (hrefl : ∀ P, R P P)
    (gs : List G) (gate : G → XorGate Reg) (label : G → Label d)
    (src dst : Reg → Label d) (e : Wire Reg (gs.map gate).length)
    (h : List.Chain' R (src e.2 ::
      (gs.filter (fun g => decide (e.2 ∈ (gate g).ports))).map label ++ [dst e.2])) :
    R (vertexLabel gs gate label src dst (wireTail (gs.map gate) e))
      (vertexLabel gs gate label src dst (wireHead (gs.map gate) e)) := by
  have hc := stageLabels_chain R hrefl
    (fun g => decide (e.2 ∈ (gate g).ports)) label gs (src e.2) (dst e.2)
    h
  have hc' : List.Chain' R (src e.2 :: wireTrace gs gate label src e.2 ++ [dst e.2]) :=
    hc
  have hi : e.1.val <
      (src e.2 :: wireTrace gs gate label src e.2 ++ [dst e.2]).length - 1 := by
    first
    | exact e.1.isLt
    | (have h_sx := e.1.isLt; simp only [List.length_cons, List.length_append, wireTrace_length,
      List.length_singleton, Nat.add_sub_cancel, List.length_map] at h_sx ⊢; exact h_sx)
    | (have h_sx := e.1.isLt; simp only [List.length_cons, List.length_append, wireTrace_length,
      List.length_singleton, Nat.add_sub_cancel, List.length_map] at h_sx; exact h_sx)
    | (simp only [List.length_cons, List.length_append, wireTrace_length,
      List.length_singleton, Nat.add_sub_cancel, List.length_map]; exact e.1.isLt)
  have he := List.chain'_iff_get.mp hc' e.1.val hi
  rcases e with ⟨i, r⟩
  rw [label_wireTail, label_wireHead]
  first
  | exact he
  | (have h_sx := he; simp only [List.get_eq_getElem, List.getElem_cons_succ] at h_sx ⊢; exact h_sx)
  | (have h_sx := he; simp only [List.get_eq_getElem, List.getElem_cons_succ] at h_sx; exact h_sx)
  | (simp only [List.get_eq_getElem, List.getElem_cons_succ]; exact he)

theorem stageLabels_property (Good : Label d → Prop)
    (active : G → Bool) (label : G → Label d) (gs : List G) (P : Label d)
    (hP : Good P) (hlabel : ∀ g ∈ gs, active g = true → Good (label g)) :
    ∀ Q ∈ stageLabels active label P gs, Good Q := by
  induction gs generalizing P with
  | nil => simp [stageLabels]
  | cons g gs ih =>
    have hnext : Good (if active g then label g else P) := by
      split_ifs with hg
      · exact hlabel g (by simp) hg
      · exact hP
    intro Q hQ
    simp only [stageLabels, List.mem_cons] at hQ
    rcases hQ with rfl | hQ
    · exact hnext
    · exact ih _ hnext (fun a ha => hlabel a (by simp [ha])) Q hQ

/-- Idempotence, symmetry, or any other vertex property can be checked on
the active history alone. Repeated private-pass labels retain the property. -/
theorem physical_edge_property
    (Good : Label d → Prop)
    (gs : List G) (gate : G → XorGate Reg) (label : G → Label d)
    (src dst : Reg → Label d) (e : Wire Reg (gs.map gate).length)
    (h : ∀ Q ∈ src e.2 ::
      (gs.filter (fun g => decide (e.2 ∈ (gate g).ports))).map label ++ [dst e.2], Good Q) :
    Good (vertexLabel gs gate label src dst (wireTail (gs.map gate) e)) ∧
      Good (vertexLabel gs gate label src dst (wireHead (gs.map gate) e)) := by
  have hs : Good (src e.2) := h _ (by simp)
  have ht : Good (dst e.2) := h _ (by simp)
  have hl : ∀ g ∈ gs, decide (e.2 ∈ (gate g).ports) = true → Good (label g) := by
    intro g hg ha
    apply h
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton]
    right
    left
    exact List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hg, ha⟩, rfl⟩
  have hp : ∀ Q ∈ wireTrace gs gate label src e.2, Good Q :=
    stageLabels_property Good _ label gs (src e.2) hs hl
  have hall : ∀ Q ∈ src e.2 :: wireTrace gs gate label src e.2 ++ [dst e.2], Good Q := by
    intro Q hQ
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | hQ | rfl
    · exact hs
    · exact hp Q hQ
    · exact ht
  rcases e with ⟨i, r⟩
  rw [label_wireTail, label_wireHead]
  constructor
  · exact hall _ (List.get_mem _ _)
  · apply hall
    exact List.mem_cons_of_mem _ (List.get_mem _ _)

#print axioms physical_edge_relation
#print axioms physical_edge_property

end
end CSL.Construction.MachineNetworkAdjacency


