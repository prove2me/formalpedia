-- Prove2me | solution 1 for AFT.FiniteDist.l1_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:24:11.857834+00:00
-- url     : https://prove2.me/submissions/7fdc5ef9-b50e-46f0-b57a-1c39f1726add

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



theorem solution (first first' : FiniteDist A) (second second' : FiniteDist B) :
    (∑ pair,|(first.prod second).weight pair-(first'.prod second').weight pair|) ≤
      (∑ a,|first.weight a-first'.weight a|)+(∑ b,|second.weight b-second'.weight b|) := by
  simp only [prod_weight,Fintype.sum_prod_type]
  calc
    _ ≤ ∑ a,∑ b,(|first.weight a-first'.weight a| *second.weight b+
        first'.weight a*|second.weight b-second'.weight b|) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      have he : first.weight a*second.weight b-first'.weight a*second'.weight b=
          (first.weight a-first'.weight a)*second.weight b+first'.weight a*(second.weight b-second'.weight b) := by ring
      rw [he]
      simpa only [abs_mul,abs_of_nonneg (second.nonneg _),abs_of_nonneg (first'.nonneg _)] using abs_add_le
        ((first.weight a-first'.weight a)*second.weight b) (first'.weight a*(second.weight b-second'.weight b))
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,second.sum_one,mul_one,← Finset.sum_mul,first'.sum_one,one_mul]





end
end FiniteDist
end AFT
