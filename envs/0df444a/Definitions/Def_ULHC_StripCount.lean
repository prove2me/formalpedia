-- Prove2me | Definitions.Def_ULHC_StripCount
-- name    : ULHC_StripCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:17:38.420103+00:00
-- url     : https://prove2.me/theorems/c273def3-cf60-4837-b209-c73a264fe531
-- title:
--   Strip Count
-- statement:
--   Definitions and structural lemmas for Strip Count, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean

import Definitions.Def_ULHC_Strip
import Theorems.Thm_ULHC_ACell_ab
import Theorems.Thm_ULHC_ACell_dk
import Theorems.Thm_ULHC_ACell_e2_ne_e1
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_deg_erase
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_Ends_ne_of
import Theorems.Thm_ULHC_back1_nb
import Theorems.Thm_ULHC_back2_nb
import Theorems.Thm_ULHC_deg_erase
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_flip_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v


set_option autoImplicit true
namespace ULHC
open Finset Classical
def StripPat (F : Finset Edge) (c : Pt) (s : Side) (n : ℕ) : Prop :=
  back c s ∈ F ∧
  (∀ j < n, (lat1 (cellJ c s j) s ∈ F ↔ j % 2 = 1) ∧ (lat2 (cellJ c s j) s ∈ F ↔ j % 2 = 1)) ∧
  (∀ j < n, (front (cellJ c s j) s ∈ F ↔ (j % 2 = 1 ↔ j + 1 < n)))
def flipCol (F : Finset Edge) (c : Pt) (s : Side) : ℕ → Finset Edge
  | 0 => F
  | n + 1 => flipCol (flip F (cellJ c s n)) c s n
lemma symmDiff_four {F E : Finset Edge} {e1 e2 l1 l2 : Edge} (hE : E = {e1, e2, l1, l2})
    (h1 : e1 ∈ F) (h2 : e2 ∈ F) (h3 : l1 ∉ F) (h4 : l2 ∉ F) :
    symmDiff F E = insert l2 (insert l1 ((F.erase e1).erase e2)) := by
  subst hE
  ext e
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
  constructor
  · rintro (⟨he, hn⟩ | ⟨hn, he⟩)
    · push Not at hn; exact Or.inr (Or.inr ⟨hn.2.1, hn.1, he⟩)
    · rcases hn with rfl | rfl | rfl | rfl
      · exact absurd h1 he
      · exact absurd h2 he
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
  · rintro (rfl | rfl | ⟨hne2, hne1, he⟩)
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr rfl)), h4⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inl rfl)), h3⟩
    · refine Or.inl ⟨he, ?_⟩
      rintro (rfl | rfl | rfl | rfl)
      · exact hne1 rfl
      · exact hne2 rfl
      · exact h3 he
      · exact h4 he
lemma ACell.flip_eq (C : ACell) {F : Finset Edge} {c : Pt}
    (hE : cellE c = {C.e1, C.e2, C.l1, C.l2})
    (h1 : C.e1 ∈ F) (h2 : C.e2 ∈ F) (h3 : C.l1 ∉ F) (h4 : C.l2 ∉ F) :
    flip F c = C.res F := symmDiff_four hE h1 h2 h3 h4
lemma deg_insert {F : Finset Edge} {e : Edge} (he : e ∉ F) (z : Pt) :
    deg (insert e F) z = deg F z + (if e.p = z ∨ e.q = z then 1 else 0) := by
  have := ULHC.deg_erase (Finset.mem_insert_self e F) z
  rw [Finset.erase_insert he] at this
  omega
lemma ACell.deg_res (C : ACell) {F : Finset Edge}
    (h1 : C.e1 ∈ F) (h2 : C.e2 ∈ F) (h3 : C.l1 ∉ F) (h4 : C.l2 ∉ F) (z : Pt) :
    deg (C.res F) z = deg F z := by
  have he2 : C.e2 ∈ F.erase C.e1 := Finset.mem_erase.2 ⟨C.e2_ne_e1, h2⟩
  have hl1 : C.l1 ∉ (F.erase C.e1).erase C.e2 := fun h => h3 (by
    simp only [Finset.mem_erase] at h; exact h.2.2)
  have l12 : C.l2 ≠ C.l1 := (C.h3.ne_of C.h4 C.ak.symm C.dk.symm).symm
  have hl2 : C.l2 ∉ insert C.l1 ((F.erase C.e1).erase C.e2) := by
    simp only [Finset.mem_insert, Finset.mem_erase, not_or]
    exact ⟨l12, fun h => h4 h.2.2⟩
  have d1 := C.h1.deg_erase h1 z
  have d2 := C.h2.deg_erase he2 z
  have d3 := deg_insert hl1 z
  have d4 := deg_insert hl2 z
  simp only [C.h3.inc_iff z] at d3
  simp only [C.h4.inc_iff z] at d4
  unfold ACell.res
  rw [d4, d3]
  have ab := C.ab
  have ad := C.ad
  have ak := C.ak
  have bd := C.bd
  have bk := C.bk
  have dk := C.dk
  by_cases za : z = C.a <;> by_cases zb : z = C.b <;> by_cases zd : z = C.d <;>
    by_cases zk : z = C.k <;> simp_all
def mkBF (c : Pt) (s : Side) : ACell where
  a := back1 c s
  b := back2 c s
  d := front1 c s
  k := front2 c s
  e1 := back c s
  e2 := front c s
  l1 := lat1 c s
  l2 := lat2 c s
  h1 := ends_back c s
  h2 := ends_front c s
  h3 := ends_lat1 c s
  h4 := ends_lat2 c s
  ad := by obtain ⟨x, y⟩ := c; cases s <;> simp [back1, front1]
  ak := by obtain ⟨x, y⟩ := c; cases s <;> simp [back1, front2]
  bd := by obtain ⟨x, y⟩ := c; cases s <;> simp [back2, front1]
  bk := by obtain ⟨x, y⟩ := c; cases s <;> simp [back2, front2]
def mkLat (c : Pt) (s : Side) : ACell where
  a := back1 c s
  b := front1 c s
  d := back2 c s
  k := front2 c s
  e1 := lat1 c s
  e2 := lat2 c s
  l1 := back c s
  l2 := front c s
  h1 := ends_lat1 c s
  h2 := ends_lat2 c s
  h3 := ends_back c s
  h4 := ends_front c s
  ad := by obtain ⟨x, y⟩ := c; cases s <;> simp [back1, back2]
  ak := by obtain ⟨x, y⟩ := c; cases s <;> simp [back1, front2]
  bd := by obtain ⟨x, y⟩ := c; cases s <;> simp [front1, back2]
  bk := by obtain ⟨x, y⟩ := c; cases s <;> simp [front1, front2]
def mkPair (c : Pt) (s : Side) : APair where
  a := back1 c s
  b := back2 c s
  m1 := front1 c s
  m2 := front2 c s
  t1 := front1 (nb c s) s
  t2 := front2 (nb c s) s
  eab := back c s
  eam := lat1 c s
  ebm := lat2 c s
  em := front c s
  et := front (nb c s) s
  emt1 := lat1 (nb c s) s
  emt2 := lat2 (nb c s) s
  hab := ends_back c s
  ham := ends_lat1 c s
  hbm := ends_lat2 c s
  hm := ends_front c s
  ht := ends_front (nb c s) s
  hmt1 := by have := ends_lat1 (nb c s) s; rwa [back1_nb] at this
  hmt2 := by have := ends_lat2 (nb c s) s; rwa [back2_nb] at this
  m1a := by obtain ⟨x, y⟩ := c; cases s <;> simp [back1, front1]
  m1b := by obtain ⟨x, y⟩ := c; cases s <;> simp [back2, front1]
  m1t1 := by obtain ⟨x, y⟩ := c; cases s <;> simp [nb, front1] <;> omega
  m1t2 := by obtain ⟨x, y⟩ := c; cases s <;> simp [nb, front1, front2]
  m2a := by obtain ⟨x, y⟩ := c; cases s <;> simp [back1, front2]
  m2b := by obtain ⟨x, y⟩ := c; cases s <;> simp [back2, front2]
  m2t1 := by obtain ⟨x, y⟩ := c; cases s <;> simp [nb, front1, front2]
  m2t2 := by obtain ⟨x, y⟩ := c; cases s <;> simp [nb, front2] <;> omega
lemma mem_flip_iff {F : Finset Edge} {c : Pt} {e : Edge} :
    e ∈ flip F c ↔ (e ∈ F ↔ e ∉ cellE c) := by
  unfold flip; rw [Finset.mem_symmDiff]; tauto
section geo2
variable (c : Pt) (s : Side)
end geo2
section pat
variable {F : Finset Edge} {c : Pt} {s : Side}
end pat
lemma inside_flip {V : Finset Pt} {F : Finset Edge} {c : Pt} (hV : Inside V F) (hc : IsCell V c) :
    Inside V (flip F c) := by
  intro e he
  rw [mem_flip_iff] at he
  by_cases hE : e ∈ cellE c
  · obtain ⟨x, y⟩ := c
    obtain ⟨h1, h2, h3, h4⟩ := hc
    simp only [cellE, Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl | rfl | rfl <;> simp [bot, top, lft, rgt, Edge.q] <;>
      exact ⟨by assumption, by assumption⟩
  · exact hV e (he.2 hE)
def Deg2 (V : Finset Pt) (F : Finset Edge) : Prop := Inside V F ∧ ∀ z ∈ V, deg F z = 2
lemma Deg2.flip {V : Finset Pt} {F : Finset Edge} (h : Deg2 V F) (C : ACell) {c : Pt}
    (hc : IsCell V c) (hE : cellE c = {C.e1, C.e2, C.l1, C.l2})
    (h1 : C.e1 ∈ F) (h2 : C.e2 ∈ F) (h3 : C.l1 ∉ F) (h4 : C.l2 ∉ F) : Deg2 V (ULHC.flip F c) := by
  refine ⟨inside_flip h.1 hc, fun z hz => ?_⟩
  rw [C.flip_eq hE h1 h2 h3 h4, C.deg_res h1 h2 h3 h4]
  exact h.2 z hz
def IsMid (c : Pt) (s : Side) (k : ℕ) (z : Pt) : Prop :=
  ∃ j, j % 2 = 1 ∧ j < k ∧ (z = front1 (cellJ c s j) s ∨ z = front2 (cellJ c s j) s)
section count
variable {V : Finset Pt} {c : Pt} {s : Side}
end count
end ULHC


