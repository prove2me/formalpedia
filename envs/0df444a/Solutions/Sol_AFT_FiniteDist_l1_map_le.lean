-- Prove2me | solution 1 for AFT.FiniteDist.l1_map_le
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:24:24.852649+00:00
-- url     : https://prove2.me/submissions/ffa4d845-3990-4dd0-9136-6893bfd1ec3f

import Definitions.Def_InfoLossLAR_Native_AFT_FiniteConcentration
import Mathlib


/-! # Total variation of actual independent finite products -/
namespace AFT.FiniteDist
end AFT.FiniteDist
section AFT
section FiniteDist
open AFT
open AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [Fintype A] [Fintype B]

theorem solution (first second : FiniteDist A) (map : A → B) :
    (∑ b,|(first.map map).weight b-(second.map map).weight b|) ≤ ∑ a,|first.weight a-second.weight a| := by
  simp only [map_weight,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ b,∑ a,|(if map a=b then first.weight a else 0)-(if map a=b then second.weight a else 0)| :=
      Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (map a)]
      · simp
      · intro b _ hba
        simp [Ne.symm hba]
      · simp







end
end FiniteDist
end AFT
