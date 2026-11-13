-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
-- name    : ProbabilityTheory_chapter_01_thm_1_2_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:52:06.528758+00:00
-- url     : https://prove2.me/theorems/30656fbe-6fae-442c-b55a-fae9df620687
-- title:
--   Chapter 1, thm_1_2: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2`: `partition_pts_monotone_core`, `partition_pts_mem_Icc_core`, `subinterval_subset_Icc_core`, `taggedSum_integrand_add`, `sourceHypotheses_integrand_add`, and 1 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

lemma partition_pts_monotone_core {a b : ℝ} (P : Partition a b)
    {i j : Fin (P.n + 1)} (hij : i ≤ j) :
  P.pts i ≤ P.pts j := by
  exact P.strict_mono.monotone hij

lemma partition_pts_mem_Icc_core {a b : ℝ} (P : Partition a b) {i : Fin (P.n + 1)} :
    P.pts i ∈ Set.Icc a b := by
  constructor
  · calc
      a = P.pts 0 := P.pts_start.symm
      _ ≤ P.pts i := partition_pts_monotone_core P (Fin.zero_le i)
  · calc
      P.pts i ≤ P.pts (Fin.last P.n) := partition_pts_monotone_core P (Fin.le_last i)
      _ = b := P.pts_end

lemma subinterval_subset_Icc_core {a b : ℝ} (P : Partition a b) {i : Fin P.n} :
    Partition.subinterval P i ⊆ Set.Icc a b := by
  intro x hx
  constructor
  ·  
    exact le_trans (partition_pts_mem_Icc_core P).1 hx.1
  ·  
    exact le_trans hx.2 (partition_pts_mem_Icc_core P).2
theorem taggedSum_integrand_add {a b : ℝ}
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (f g alpha : ℝ → ℝ) :
  taggedSum P tags (fun x => f x + g x) alpha =
      taggedSum P tags f alpha + taggedSum P tags g alpha := by
  unfold taggedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring
theorem sourceHypotheses_integrand_add {a b : ℝ} {f g alpha : ℝ → ℝ}
    (hf : SourceHypotheses a b f alpha)
    (hg : SourceHypotheses a b g alpha) :
    SourceHypotheses a b (fun x => f x + g x) alpha := by
  rcases hf with ⟨hab, hfAbove, hfBelow, hmono⟩
  rcases hg with ⟨_habg, hgAbove, hgBelow, _hmonog⟩
  refine ⟨hab, ?_, ?_, hmono⟩
  · refine BddAbove.mono ?_ (hfAbove.add hgAbove)
    rintro y ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, g x, ⟨x, hx, rfl⟩, rfl⟩
  · refine BddBelow.mono ?_ (hfBelow.add hgBelow)
    rintro y ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, g x, ⟨x, hx, rfl⟩, rfl⟩
theorem taggedCommonLimit_integrand_add {a b : ℝ} {f g alpha : ℝ → ℝ}
    {Lf Lg : ℝ}
    (hf : TaggedCommonLimit a b f alpha Lf)
    (hg : TaggedCommonLimit a b g alpha Lg) :
    TaggedCommonLimit a b (fun x => f x + g x) alpha (Lf + Lg) := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨hsg, hlimg⟩
  refine ⟨sourceHypotheses_integrand_add hsf hsg, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro P tags htags hmesh
  have hmeshf : P.mesh < δf := lt_of_lt_of_le hmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hmesh (min_le_right δf δg)
  have hPf := Hf P tags htags hmeshf
  have hPg := Hg P tags htags hmeshg
  have hadd :
      taggedSum P tags (fun x => f x + g x) alpha - (Lf + Lg) =
        (taggedSum P tags f alpha - Lf) +
          (taggedSum P tags g alpha - Lg) := by
    rw [taggedSum_integrand_add]
    ring
  calc
    |taggedSum P tags (fun x => f x + g x) alpha - (Lf + Lg)| =
        |(taggedSum P tags f alpha - Lf) +
          (taggedSum P tags g alpha - Lg)| := by
      rw [hadd]
    _ ≤ |taggedSum P tags f alpha - Lf| +
        |taggedSum P tags g alpha - Lg| := abs_add_le _ _
    _ < eps := by
      have hlt :
          |taggedSum P tags f alpha - Lf| +
            |taggedSum P tags g alpha - Lg| < eps / 2 + eps / 2 :=
        add_lt_add hPf hPg
      simpa using hlt

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

end Partition

end Darboux_fundamental_result


