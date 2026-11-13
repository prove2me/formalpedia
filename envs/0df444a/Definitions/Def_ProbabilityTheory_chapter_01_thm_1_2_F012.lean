-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F012
-- name    : ProbabilityTheory_chapter_01_thm_1_2_F012
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:50:54.473658+00:00
-- url     : https://prove2.me/theorems/2c197086-148d-4250-a4ce-03f5d08c9166
-- title:
--   Chapter 1, thm_1_2: supporting Lean bundle F012
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2`: `Refinement.biUnion_block_eq_univ`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F011
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

private lemma Refinement.mem_block_iff_for_biUnion
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i : Fin P.n} {j : Fin P'.n} :
    j ∈ R.block i ↔
      (R.index i.castSucc).val ≤ j.val ∧
      j.val < (R.index i.succ).val := by
  classical
  unfold Refinement.block
  dsimp
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨t, _htmem, htj⟩

    have htlt :
        t.1 < (R.index i.succ).val - (R.index i.castSucc).val := by
      exact Finset.mem_range.mp t.2

    have hjval :
        j.val = (R.index i.castSucc).val + t.1 := by
      exact (congrArg Fin.val htj).symm

    constructor
    · rw [hjval]
      omega
    · rw [hjval]
      omega

  · intro hj
    rcases hj with ⟨hlo, hhi⟩

    let tnat : ℕ := j.val - (R.index i.castSucc).val

    have htlt :
        tnat < (R.index i.succ).val - (R.index i.castSucc).val := by
      dsimp [tnat]
      omega

    let t :
        {x // x ∈ Finset.range
          ((R.index i.succ).val - (R.index i.castSucc).val)} :=
      ⟨tnat, Finset.mem_range.mpr htlt⟩

    apply Finset.mem_image.mpr
    refine ⟨t, ?_, ?_⟩
    · exact Finset.mem_attach _ _
    · apply Fin.ext
      dsimp [t, tnat]
      omega

private lemma Refinement.exists_mem_block_for_biUnion
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    (j : Fin P'.n) :
    ∃ i : Fin P.n, j ∈ R.block i := by
  classical

  let Q : ℕ → Prop :=
    fun q =>
      ∃ hq : q < P.n + 1,
        j.val < (R.index ⟨q, hq⟩).val

  have hQ : ∃ q : ℕ, Q q := by
    refine ⟨P.n, ?_⟩
    dsimp [Q]
    refine ⟨by omega, ?_⟩

    have hlast_fin :
        (⟨P.n, by omega⟩ : Fin (P.n + 1)) = Fin.last P.n := by
      apply Fin.ext
      simp

    have hlast_val :
        (R.index (⟨P.n, by omega⟩ : Fin (P.n + 1))).val = P'.n := by
      rw [hlast_fin, Refinement.index_last R]
      rfl

    rw [hlast_val]
    exact j.isLt

  let q : ℕ := Nat.find hQ

  have hqspec : Q q := Nat.find_spec hQ

  rcases hqspec with ⟨hq_bound, hj_lt_q⟩

  have hq_pos : 0 < q := by
    by_contra hnot
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hnot

    have hfin0 :
        (⟨q, hq_bound⟩ : Fin (P.n + 1)) =
          (0 : Fin (P.n + 1)) := by
      apply Fin.ext
      simp [hq0]

    have : j.val < 0 := by
      calc
        j.val < (R.index (⟨q, hq_bound⟩ : Fin (P.n + 1))).val := hj_lt_q
        _ = (R.index (0 : Fin (P.n + 1))).val := by
          rw [hfin0]
        _ = 0 := by
          rw [Refinement.index_zero R]
          rfl

    omega

  have hprev_lt_q : q - 1 < q := by
    omega

  have hnot_prev : ¬ Q (q - 1) := by
    exact Nat.find_min hQ hprev_lt_q

  have hprev_bound : q - 1 < P.n + 1 := by
    omega

  have hprev_le :
      (R.index (⟨q - 1, hprev_bound⟩ : Fin (P.n + 1))).val ≤ j.val := by
    by_contra hnot_le
    have hlt :
        j.val <
          (R.index (⟨q - 1, hprev_bound⟩ : Fin (P.n + 1))).val :=
      Nat.lt_of_not_ge hnot_le

    exact hnot_prev ⟨hprev_bound, hlt⟩

  let i : Fin P.n := ⟨q - 1, by omega⟩

  refine ⟨i, ?_⟩

  apply (Refinement.mem_block_iff_for_biUnion R (i := i) (j := j)).mpr
  constructor
  · have hcast :
        i.castSucc =
          (⟨q - 1, hprev_bound⟩ : Fin (P.n + 1)) := by
      apply Fin.ext
      simp [i]

    simpa [hcast] using hprev_le

  · have hsucc :
        i.succ =
          (⟨q, hq_bound⟩ : Fin (P.n + 1)) := by
      apply Fin.ext
      simp [i]
      omega

    simpa [hsucc] using hj_lt_q

lemma Refinement.biUnion_block_eq_univ
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P') :
    (Finset.univ.biUnion fun i : Fin P.n => R.block i)
      =
    (Finset.univ : Finset (Fin P'.n)) := by
  classical

  ext j
  constructor
  · intro _hj
    exact Finset.mem_univ j

  · intro _hj
    rcases Refinement.exists_mem_block_for_biUnion R j with ⟨i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
namespace Partition

end Partition

end Darboux_fundamental_result


