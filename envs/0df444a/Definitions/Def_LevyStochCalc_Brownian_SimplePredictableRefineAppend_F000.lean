-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineAppend_F000
-- name    : LevyStochCalc_Brownian_SimplePredictableRefineAppend_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:55:58.989782+00:00
-- url     : https://prove2.me/theorems/8fde871a-9aa0-4b0c-aeef-028bd2e38870
-- title:
--   Source declarations: LevyStochCalc.Brownian.SimplePredictableRefineAppend
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.SimplePredictableRefineAppend. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F001
import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F003
import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F004

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Zero-extension of a simple predictable to a larger horizon

Appending one interval carrying the coefficient `0`
(`SimplePredictable.appendInterval`) turns a `SimplePredictable Ω T` into a
`SimplePredictable Ω T'` on a larger horizon with the same `eval`, the same
simple integral and the same adaptedness, so that two approximants on different
horizons can be compared on a common endpoint.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- `Fin.snoc f a` is strictly monotone when `f` is and `f (last) < a`. -/
lemma strictMono_snoc {n : ℕ} {α : Type*} [Preorder α] {f : Fin (n + 1) → α}
    (hf : StrictMono f) {a : α} (ha : f (Fin.last n) < a) :
    StrictMono (Fin.snoc f a) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hf (by rwa [Fin.castSucc_lt_castSucc_iff] at hij)
    · exact absurd hij (not_lt.mpr (Fin.le_last _))
  · rw [Fin.snoc_last]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
      exact lt_of_le_of_lt (hf.monotone (Fin.le_last i')) ha
    · exact absurd hij (lt_irrefl _)
/-- **Zero-extension to a larger horizon.** Append one interval `(H_last, T']`
carrying coefficient `0`, producing a `SimplePredictable` on the larger horizon
`T'` whose `eval` and `simpleIntegral` are unchanged. Lets two different-horizon
approximants be put on a common endpoint for the difference isometry. -/
noncomputable def SimplePredictable.appendInterval
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') : SimplePredictable Ω T' where
  N := H.N + 1
  partition := Fin.snoc H.partition T'
  partition_zero := by rw [Fin.snoc_apply_zero]; exact H.partition_zero
  partition_le_T := by rw [Fin.snoc_last]
  partition_strictMono := strictMono_snoc H.partition_strictMono hlt
  ξ := Fin.snoc H.ξ (fun _ => 0)
  ξ_bounded := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · obtain ⟨M, hM⟩ := H.ξ_bounded i'
      exact ⟨M, fun ω => by rw [Fin.snoc_castSucc]; exact hM ω⟩
    · exact ⟨0, fun ω => by rw [Fin.snoc_last]; simp⟩
  ξ_measurable := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]; exact H.ξ_measurable i'
    · rw [Fin.snoc_last]; exact measurable_const
lemma SimplePredictable.appendInterval_partition_eq
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') :
    (H.appendInterval hlt).partition = Fin.snoc H.partition T' := rfl
lemma SimplePredictable.appendInterval_xi_eq
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') :
    (H.appendInterval hlt).ξ = Fin.snoc H.ξ (fun _ => 0) := rfl
lemma SimplePredictable.appendInterval_partition_last
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') :
    (H.appendInterval hlt).partition (Fin.last (H.N + 1)) = T' := by
  rw [H.appendInterval_partition_eq hlt]
  exact Fin.snoc_last (α := fun _ => ℝ) T' H.partition
/-- Index identity used to relate the appended partition's `castSucc`/`succ`
to the original partition. -/
private lemma appendInterval_succ_castSucc {n : ℕ} (i : Fin n) :
    (Fin.castSucc i).succ = Fin.castSucc i.succ := Fin.ext rfl
/-- Pointwise values of the appended partition / coefficients. -/
lemma SimplePredictable.appendInterval_partition_castSucc
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') (j : Fin (H.N + 1)) :
    (H.appendInterval hlt).partition (Fin.castSucc j) = H.partition j := by
  change (Fin.snoc (α := fun _ => ℝ) H.partition T') (Fin.castSucc j) = H.partition j
  exact @Fin.snoc_castSucc (H.N + 1) (fun _ => ℝ) T' H.partition j
lemma SimplePredictable.appendInterval_xi_castSucc
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') (j : Fin H.N) :
    (H.appendInterval hlt).ξ (Fin.castSucc j) = H.ξ j := by
  rw [H.appendInterval_xi_eq hlt]; simp only [Fin.snoc_castSucc]
lemma SimplePredictable.appendInterval_xi_last
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') :
    (H.appendInterval hlt).ξ (Fin.last H.N) = (fun _ : Ω => (0 : ℝ)) := by
  rw [H.appendInterval_xi_eq hlt]; simp only [Fin.snoc_last]
end LevyStochCalc.Brownian.Ito


