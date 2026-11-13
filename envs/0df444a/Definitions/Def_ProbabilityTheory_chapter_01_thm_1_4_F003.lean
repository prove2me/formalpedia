-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F003
-- name    : ProbabilityTheory_chapter_01_thm_1_4_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:25:56.2102+00:00
-- url     : https://prove2.me/theorems/f97fe715-02fa-4a3d-ad59-fa64be02eb33
-- title:
--   Chapter 1, thm_1_4: supporting Lean bundle F003
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_4`: `ptNat`, `ptNat_zero`, `ptNat_last`, `ptNat_of_lt`, `ptNat_succ_of_lt`, and 1 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F001
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators Pointwise Interval

noncomputable section

namespace Thm_1_4

private noncomputable def ptNat {a b : ℝ} (P : Partition a b) (k : ℕ) : ℝ :=
  if hk : k ≤ P.n then
    P.pts ⟨k, Nat.lt_succ_of_le hk⟩
  else
    P.pts (Fin.last P.n)
private lemma ptNat_zero {a b : ℝ} (P : Partition a b) :
    ptNat P 0 = a := by
  unfold ptNat
  rw [dif_pos (Nat.zero_le P.n)]
  simpa using P.pts_start
private lemma ptNat_last {a b : ℝ} (P : Partition a b) :
    ptNat P P.n = b := by
  unfold ptNat
  rw [dif_pos le_rfl]
  have hfin :
      (⟨P.n, Nat.lt_succ_self P.n⟩ : Fin (P.n + 1)) = Fin.last P.n := by
    ext
    simp
  simpa [hfin] using P.pts_end
private lemma ptNat_of_lt {a b : ℝ} (P : Partition a b) {k : ℕ}
    (hk : k < P.n) :
    ptNat P k = P.pts (Fin.castSucc (⟨k, hk⟩ : Fin P.n)) := by
  unfold ptNat
  rw [dif_pos (le_of_lt hk)]
  congr
private lemma ptNat_succ_of_lt {a b : ℝ} (P : Partition a b) {k : ℕ}
    (hk : k < P.n) :
    ptNat P (k + 1) = P.pts (Fin.succ (⟨k, hk⟩ : Fin P.n)) := by
  unfold ptNat
  rw [dif_pos (Nat.succ_le_of_lt hk)]
  congr

private lemma partition_integral_sum {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (P : Partition a b) :
    (∑ i : Fin P.n,
        ∫ x in P.pts i.castSucc..P.pts i.succ, g x) =
      ∫ x in a..b, g x := by
  classical
  rw [Finset.sum_fin_eq_sum_range]

  have hcellIntNat :
      ∀ k < P.n, IntervalIntegrable g volume (ptNat P k) (ptNat P (k + 1)) := by
    intro k hk
    let i : Fin P.n := ⟨k, hk⟩
    have huv : P.pts i.castSucc ≤ P.pts i.succ :=
      le_of_lt (P.strict_mono Fin.castSucc_lt_succ)
    have hgcell :
        ContinuousOn g (Set.Icc (P.pts i.castSucc) (P.pts i.succ)) :=
      hg.mono (DarbouxRS.subinterval_subset_Icc_core P (i := i))
    have hInt :
        IntervalIntegrable g volume (P.pts i.castSucc) (P.pts i.succ) :=
      ContinuousOn.intervalIntegrable_of_Icc huv hgcell

    have hleft : ptNat P k = P.pts i.castSucc := by
      rw [ptNat_of_lt P hk]

    have hright : ptNat P (k + 1) = P.pts i.succ := by
      rw [ptNat_succ_of_lt P hk]

    simpa [hleft, hright] using hInt

  have hsum0 :=
    intervalIntegral.sum_integral_adjacent_intervals hcellIntNat

  have hsum :
      (∑ k ∈ Finset.range P.n,
          ∫ x in ptNat P k..ptNat P (k + 1), g x) =
        ∫ x in a..b, g x := by
    simpa [ptNat_zero, ptNat_last] using hsum0

  trans
      (∑ k ∈ Finset.range P.n,
          ∫ x in ptNat P k..ptNat P (k + 1), g x)
  · refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < P.n := Finset.mem_range.mp hk
    rw [dif_pos hklt]
    rw [ptNat_of_lt P hklt, ptNat_succ_of_lt P hklt]

  · exact hsum

end Thm_1_4


