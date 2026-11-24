-- Prove2me | Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventProperties
-- name    : CSL_Circuit_MemoryAccess_PhysicalFrameEventProperties
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:03:09.129797+00:00
-- url     : https://prove2.me/theorems/25d3643f-f87d-4a69-906a-e19b679195bd
-- title:
--   Coded sorting library: Circuit / MemoryAccess / PhysicalFrameEventProperties
-- statement:
--   Module `CodedSorting.Circuit.MemoryAccess.PhysicalFrameEventProperties` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.MemoryAccess.PhysicalFrameEventProperties

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameWordData

namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
universe u

theorem eventVisits_append (r : Nat) (xs ys : List FrameEvent) :
    eventVisits r (xs ++ ys) = eventVisits r xs ++ eventVisits r ys := by
  simp [eventVisits]

theorem eventVisits_reverse (r : Nat) (xs : List FrameEvent) :
    eventVisits r xs.reverse = (eventVisits r xs).reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, eventVisits_append, ih]
    by_cases h : r ∈ x.ports <;> simp [eventVisits, h]

theorem eventVisits_map_reverse {A : Type u} (r : Nat) (xs : List A) (f : A → FrameEvent) :
    eventVisits r (xs.reverse.map f) = (eventVisits r (xs.map f)).reverse := by
  rw [List.map_reverse, eventVisits_reverse]

theorem eventVisits_eq_nil (r : Nat) (xs : List FrameEvent)
    (h : ∀ e ∈ xs, r ∉ e.ports) : eventVisits r xs = [] := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    have he := h e (by simp)
    have hs := ih (fun a ha => h a (by simp [ha]))
    simpa [eventVisits, he] using hs

theorem copyVisits_reverse (r : Fin 661) :
    (eventVisits r.val ((List.range 9).map copyEvent)).reverse =
      eventVisits r.val ((List.range 9).map copyEvent) := by
  have h : ∀ i : Fin 661,
      (eventVisits i.val ((List.range 9).map copyEvent)).reverse =
        eventVisits i.val ((List.range 9).map copyEvent) := by
    decide +kernel
  exact h r

theorem copyVisits_nil_of_low (r : Nat) (hr : r < 222) :
    eventVisits r ((List.range 9).map copyEvent) = [] := by
  apply eventVisits_eq_nil
  intro e he
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
  simp only [copyEvent, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem scatterVisits_nil_of_high (r : Nat) (hr : 222 ≤ r) (hr' : r < 661)
    (hs : ∀ g ∈ physicalScatter, g.destination < 222) :
    eventVisits r (physicalScatter.map scatterEvent) = [] := by
  apply eventVisits_eq_nil
  intro e he
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
  have hd := hs g hg
  simp only [scatterEvent, List.mem_cons, List.mem_map]
  rintro (h | ⟨t, ht, h⟩) <;> omega

theorem middle_visits_reverse_abstract (r : Nat)
    (before copies scatter after : List FrameEvent)
    (hc : (eventVisits r copies).reverse = eventVisits r copies)
    (hd : eventVisits r copies = [] ∨ eventVisits r scatter = []) :
    (eventVisits r (after.reverse ++ copies ++ scatter.reverse ++ before.reverse)).reverse =
      eventVisits r (before ++ copies ++ scatter ++ after) := by
  simp only [eventVisits_append, eventVisits_reverse, List.reverse_append, List.reverse_reverse]
  rw [hc]
  rcases hd with hd | hd <;> simp only [hd, List.nil_append, List.append_nil, List.append_assoc]

/-- The exact original-register histories of the physical middle word are
reversals of the forward histories. Fresh copies commute with scatter on
original histories because these batches touch disjoint original registers. -/
theorem middle_original_visits_reverse_of_shape (r : Fin 661)
    (hs : ∀ g ∈ physicalScatter, g.destination < 222) :
    (eventVisits r.val middleEvents).reverse = eventVisits r.val forwardEvents := by
  have hr := r.isLt
  have hd : eventVisits r.val ((List.range 9).map copyEvent) = [] ∨
      eventVisits r.val (physicalScatter.map scatterEvent) = [] := by
    by_cases hl : r.val < 222
    · exact Or.inl (copyVisits_nil_of_low r.val hl)
    · exact Or.inr (scatterVisits_nil_of_high r.val (by omega) hr hs)
  have he := middle_visits_reverse_abstract r.val
    (physicalPrefix.map ordinaryEvent) ((List.range 9).map copyEvent)
    (physicalScatter.map scatterEvent) (physicalSuffix.map ordinaryEvent)
    (copyVisits_reverse r) hd
  change (eventVisits r.val
    (physicalSuffix.reverse.map ordinaryEvent ++ (List.range 9).map copyEvent ++
      physicalScatter.reverse.map scatterEvent ++ physicalPrefix.reverse.map ordinaryEvent)).reverse = _
  rw [List.map_reverse (l := physicalSuffix) (f := ordinaryEvent),
    List.map_reverse (l := physicalScatter) (f := scatterEvent),
    List.map_reverse (l := physicalPrefix) (f := ordinaryEvent)]
  exact he

end CSL.Construction.PhysicalFramePaths


