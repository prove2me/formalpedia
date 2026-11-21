-- Prove2me | Definitions.Def_Cage87_Bridge
-- name    : Cage87_Bridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T20:25:31.876328+00:00
-- url     : https://prove2.me/theorems/fd14497e-98cb-4136-94d2-5e7b41fd1978
-- title:
--   Bridge
-- statement:
--   Definitions and structural lemmas for Bridge, from arhancanli and contributors's pinned 8-regular graph of girth 7 on 768 vertices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Bridge.lean

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic.IntervalCases
public import Theorems.Thm_Cage87_wf_ok

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Cage87
open SimpleGraph
theorem wfV_of_wfOk (h : wfOk adj 768 8 = true) (v : Nat) (hv : v < 768) : wfV adj 768 8 v = true := by
  simp only [wfOk, List.all_eq_true, List.mem_range] at h
  exact h v hv
section
variable {v : Nat} (hv : v < 768)
include hv
theorem nb_prop {x : Nat} (hx : x ∈ nb adj v) : x < 768 ∧ x ≠ v ∧ v ∈ nb adj x := by
  have h := wfV_of_wfOk wf_ok v hv
  simp only [wfV, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 x hx
  simp only [Nat.blt_eq, Bool.not_eq_true', List.contains_iff_mem] at this
  refine ⟨this.1.1, fun e => ?_, this.2⟩
  have h' := this.1.2
  rw [e] at h'
  simp at h'
end
noncomputable def G : SimpleGraph (Fin 768) where
  Adj u v := v.val ∈ nb adj u.val
  symm := ⟨fun u _ h => (nb_prop u.2 h).2.2⟩
  loopless := ⟨fun u h => (nb_prop u.2 h).2.1 rfl⟩
noncomputable instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (v.val ∈ nb adj u.val))
def cycle7 : G.Walk 0 0 :=
  Walk.cons (v := 14) (by decide +kernel) <| Walk.cons (v := 398) (by decide +kernel) <|
    Walk.cons (v := 67) (by decide +kernel) <| Walk.cons (v := 468) (by decide +kernel) <|
      Walk.cons (v := 83) (by decide +kernel) <| Walk.cons (v := 387) (by decide +kernel) <|
        Walk.cons (v := 0) (by decide +kernel) Walk.nil
end Cage87


