-- Prove2me | Definitions.Def_StepMachines_Math_CodeMore
-- name    : StepMachines_Math_CodeMore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:33:34.279088+00:00
-- url     : https://prove2.me/theorems/354d5971-bf16-48b2-adce-28eac2c04cb8
-- title:
--   Code More
-- statement:
--   Definitions and structural lemmas for Code More, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeMore.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Mathlib.Data.List.GetD
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words


set_option autoImplicit false
section
namespace Groundwork
open Finset
variable {X Y : Type*}
namespace Code
variable {S : Finset X} {n : ℕ}
public noncomputable def enc (c : Code S n) (x : X) : List Bool := Function.invFunOn c.dec c.D x
public theorem enc_mem (c : Code S n) {x : X} (hx : x ∈ S) : c.enc x ∈ c.D :=
  mem_coe.1 (Function.invFunOn_mem (c.bij.surjOn (mem_coe.2 hx)))
public theorem dec_enc (c : Code S n) {x : X} (hx : x ∈ S) : c.dec (c.enc x) = x :=
  Function.invFunOn_eq (c.bij.surjOn (mem_coe.2 hx))
public theorem length_enc (c : Code S n) {x : X} (hx : x ∈ S) : (c.enc x).length = n := c.len _ (c.enc_mem hx)
theorem block_zero (m : ℕ) (w : List Bool) : block m 0 w = w.take m := by simp [block]
theorem block_succ (m j : ℕ) (w : List Bool) : block m (j + 1) w = block m j (w.drop m) := by
  rw [block, block, List.drop_drop]
  congr 2
  ring
theorem block_ext (m r : ℕ) (w w' : List Bool) (hw : w.length = r * m) (hw' : w'.length = r * m)
    (h : ∀ j < r, block m j w = block m j w') : w = w' := by
  induction r generalizing w w' with
  | zero =>
    rw [Nat.zero_mul, List.length_eq_zero_iff] at hw hw'
    rw [hw, hw']
  | succ r ih =>
    rw [Nat.succ_mul] at hw hw'
    have h0 := h 0 (by omega)
    rw [block_zero, block_zero] at h0
    have h1 := ih (w.drop m) (w'.drop m) (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega)
      fun j hj => by rw [← block_succ, ← block_succ]; exact h (j + 1) (by omega)
    rw [← List.take_append_drop m w, h0, h1, List.take_append_drop]
theorem exists_blocks (m r : ℕ) (v : ℕ → List Bool) (hv : ∀ j < r, (v j).length = m) :
    ∃ w : List Bool, w.length = r * m ∧ ∀ j < r, block m j w = v j := by
  induction r generalizing v with
  | zero => exact ⟨[], by simp, fun j hj => absurd hj (by omega)⟩
  | succ r ih =>
    obtain ⟨w, hw, hb⟩ := ih (fun j => v (j + 1)) fun j hj => hv (j + 1) (by omega)
    have h0 := hv 0 (by omega)
    refine ⟨v 0 ++ w, by rw [List.length_append, h0, hw, Nat.succ_mul]; omega, fun j hj => ?_⟩
    cases j with
    | zero => rw [block_zero, ← h0, List.take_left]
    | succ j =>
      have hd : (v 0 ++ w).drop m = w := by rw [← h0, List.drop_left]
      rw [block_succ, hd]
      exact hb j (by omega)
@[expose] public def blocks {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (pos : ι ≃ Fin r) {m : ℕ} (c : Code S m) :
    Code (Fintype.piFinset fun _ : ι => S) (r * m) where
  D := (words (r * m)).filter fun w => ∀ i, block m (pos i) w ∈ c.D
  dec w i := c.dec (block m (pos i) w)
  len w h := mem_words.1 (mem_filter.1 h).1
  bij := by
    refine ⟨fun w hw => ?_, fun w hw w' hw' h => ?_, fun x hx => ?_⟩
    · have hw := (mem_filter.1 (mem_coe.1 hw)).2
      exact mem_coe.2 (Fintype.mem_piFinset.2 fun i => c.bij.mapsTo (hw i))
    · obtain ⟨hl, hw⟩ := mem_filter.1 (mem_coe.1 hw)
      obtain ⟨hl', hw'⟩ := mem_filter.1 (mem_coe.1 hw')
      refine block_ext m r w w' (mem_words.1 hl) (mem_words.1 hl') fun j hj => ?_
      have h1 := c.bij.injOn (hw (pos.symm ⟨j, hj⟩)) (hw' (pos.symm ⟨j, hj⟩)) (congrFun h (pos.symm ⟨j, hj⟩))
      simpa using h1
    · have hx := Fintype.mem_piFinset.1 (mem_coe.1 hx)
      obtain ⟨w, hl, hb⟩ := exists_blocks m r (fun j => if hj : j < r then c.enc (x (pos.symm ⟨j, hj⟩)) else [])
        fun j hj => by simp only [dif_pos hj]; exact c.length_enc (hx _)
      have hb' : ∀ i, block m (pos i) w = c.enc (x i) := fun i => by
        rw [hb _ (pos i).2]; simp
      refine ⟨w, mem_coe.2 (mem_filter.2 ⟨mem_words.2 hl, fun i => ?_⟩), funext fun i => ?_⟩
      · rw [hb']; exact c.enc_mem (hx i)
      · change c.dec (block m (pos i) w) = x i
        rw [hb', c.dec_enc (hx i)]
@[expose] public def subsets {ι : Type*} [DecidableEq ι] (Ω : Finset ι) (M : ℕ) (idx : ι → ℕ)
    (_h : Set.BijOn idx Ω (range M)) : Code Ω.powerset M where
  D := words M
  dec τ := Ω.filter fun ω => τ.getD (idx ω) false = true
  len _ h := mem_words.1 h
  bij := by
    refine ⟨fun τ _ => mem_coe.2 (mem_powerset.2 (filter_subset _ _)), fun τ hτ τ' hτ' h => ?_, fun A hA => ?_⟩
    · have l := mem_words.1 (mem_coe.1 hτ)
      have l' := mem_words.1 (mem_coe.1 hτ')
      refine List.ext_getElem (l.trans l'.symm) fun j hj hj' => ?_
      obtain ⟨ω, hω, rfl⟩ := _h.surjOn (mem_coe.2 (mem_range.2 (l ▸ hj)))
      have h1 := Finset.ext_iff.1 h ω
      simp only [mem_filter, mem_coe.1 hω, true_and, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at h1
      exact Bool.eq_iff_iff.2 h1
    · have hA := mem_powerset.1 (mem_coe.1 hA)
      refine ⟨(List.range M).map fun j => decide (∃ ω ∈ A, idx ω = j), mem_coe.2 (mem_words.2 (by simp)), ?_⟩
      ext ω
      simp only [mem_filter]
      constructor
      · rintro ⟨hω, h1⟩
        have hlt : idx ω < M := mem_range.1 (_h.mapsTo (mem_coe.2 hω))
        rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at h1
        simp only [List.getElem_map, List.getElem_range, decide_eq_true_eq] at h1
        obtain ⟨ω', hω', e⟩ := h1
        rwa [← _h.injOn (mem_coe.2 (hA hω')) (mem_coe.2 hω) e]
      · intro hω
        have hlt : idx ω < M := mem_range.1 (_h.mapsTo (mem_coe.2 (hA hω)))
        refine ⟨hA hω, ?_⟩
        rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
        simp only [List.getElem_map, List.getElem_range, decide_eq_true_eq]
        exact ⟨ω, hω, rfl⟩
end Code
end Groundwork


