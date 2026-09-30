-- Prove2me | solution 1 for AssignmentGame.CoreCorners.core_coord_diff_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:52:46.60869+00:00
-- url     : https://prove2.me/submissions/7a105bad-0158-480d-9ed5-6b7f6a301e70

import Definitions.Def_AssignmentGame_CoreCorners_Game
import Mathlib.Tactic
set_option autoImplicit false
open AssignmentGame.CoreCorners Finset

private theorem worth_nonneg {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (A : Finset M) (B : Finset N) : 0 ≤ worth a A B := by
  have h := Finset.le_sup' (f := fun P : Finset (M × N) => ∑ p ∈ P, a p.1 p.2) (empty_mem_matchings A B)
  simpa [worth] using h

private theorem core_nonneg {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (p : (M → ℝ) × (N → ℝ)) (hp : p ∈ core a) :
    (∀ i, 0 ≤ p.1 i) ∧ (∀ j, 0 ≤ p.2 j) := by
  classical
  constructor
  · intro i
    have hi := (worth_nonneg a {i} ∅).trans (hp.2 {i} ∅)
    simpa using hi
  · intro j
    have hj := (worth_nonneg a ∅ {j}).trans (hp.2 ∅ {j})
    simpa using hj

private theorem core_bound {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (p : (M → ℝ) × (N → ℝ)) (hp : p ∈ core a) :
    (∀ i, p.1 i ≤ worth a univ univ) ∧ (∀ j, p.2 j ≤ worth a univ univ) := by
  classical
  obtain ⟨hu, hv⟩ := core_nonneg a p hp
  have hu0 := Finset.sum_nonneg (fun i (_ : i ∈ (univ : Finset M)) => hu i)
  have hv0 := Finset.sum_nonneg (fun j (_ : j ∈ (univ : Finset N)) => hv j)
  constructor
  · intro i
    have hi := Finset.single_le_sum (fun k (_ : k ∈ (univ : Finset M)) => hu k) (mem_univ i)
    linarith [hp.1]
  · intro j
    have hj := Finset.single_le_sum (fun k (_ : k ∈ (univ : Finset N)) => hv k) (mem_univ j)
    linarith [hp.1]

private theorem abs_sub_le_width (S : Set ℝ) (hSlo : BddBelow S) (hShi : BddAbove S)
    (x y : ℝ) (hx : x ∈ S) (hy : y ∈ S) : |x-y| ≤ sSup S - sInf S := by
  rw [abs_sub_le_iff]
  have hxlo := csInf_le hSlo hx
  have hylo := csInf_le hSlo hy
  have hxhi := le_csSup hShi hx
  have hyhi := le_csSup hShi hy
  constructor <;> linarith

theorem solution {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (u' u'' : M → ℝ) (v' v'' : N → ℝ)
    (h' : (u', v') ∈ core a) (h'' : (u'', v'') ∈ core a) :
    (∀ i : M, |u' i - u'' i| ≤ uHi a i - uLo a i) ∧
    (∀ j : N, |v' j - v'' j| ≤ vHi a j - vLo a j) := by
  constructor
  · intro i
    apply abs_sub_le_width
    · refine ⟨0, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      exact (core_nonneg a p hp).1 i
    · refine ⟨worth a univ univ, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      exact (core_bound a p hp).1 i
    · exact ⟨(u',v'), h', rfl⟩
    · exact ⟨(u'',v''), h'', rfl⟩
  · intro j
    apply abs_sub_le_width
    · refine ⟨0, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      exact (core_nonneg a p hp).2 j
    · refine ⟨worth a univ univ, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      exact (core_bound a p hp).2 j
    · exact ⟨(u',v'), h', rfl⟩
    · exact ⟨(u'',v''), h'', rfl⟩
