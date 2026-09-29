-- Prove2me | solution 1 for AffineDilatation.isSMulRegular_and_map_eq_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1395f9de-22dd-5037-a0b8-f07bf3362f93

import Mathlib
import Definitions.Def_RingTheory_AffineDilatation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AffineDilatation_isSMulRegular_and_map_eq_span_singleton

set_option autoImplicit false

universe u

namespace AffineDilatation
p2m_export "AffineDilatation" "Ring divElem algebraMap_mul_divElem"
namespace BasicProps
p2m_open "AffineDilatation"

open scoped nonZeroDivisors

variable {A : Type u} [CommRing A]

theorem isSMulRegular (I : Ideal A) (a : A) : IsSMulRegular (Ring I a) a := by
  intro x y hxy
  apply Subtype.ext
  have h : algebraMap A (Localization.Away a) a * (x : Localization.Away a) =
      algebraMap A (Localization.Away a) a * (y : Localization.Away a) := by
    have := congrArg (fun z : Ring I a => (z : Localization.Away a)) hxy
    simpa [Algebra.smul_def] using this
  exact (IsLocalization.Away.algebraMap_isUnit a).mul_left_cancel h

theorem algebraMap_mem_nonZeroDivisors (I : Ideal A) (a : A) :
    algebraMap A (Ring I a) a ∈ (Ring I a)⁰ := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  refine isSMulRegular I a (?_ : a • x = a • (0 : Ring I a))
  rw [Algebra.smul_def, Algebra.smul_def, mul_zero, mul_comm]
  exact hx

theorem map_eq_span (I : Ideal A) (a : A) (ha : a ∈ I) :
    I.map (algebraMap A (Ring I a)) = Ideal.span {algebraMap A (Ring I a) a} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    exact ⟨divElem I a g hg, by rw [mul_comm, algebraMap_mul_divElem]⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ ha

end AffineDilatation.BasicProps

theorem solution
    {A : Type u} [CommRing A] (I : Ideal A) (a : A) (ha : a ∈ I) :
    IsSMulRegular (AffineDilatation.Ring I a) a ∧
      I.map (algebraMap A (AffineDilatation.Ring I a)) =
        Ideal.span {algebraMap A (AffineDilatation.Ring I a) a} :=
  ⟨AffineDilatation.BasicProps.isSMulRegular I a, AffineDilatation.BasicProps.map_eq_span I a ha⟩

end S_AffineDilatation_isSMulRegular_and_map_eq_span_singleton
end P2MW
export P2MW.S_AffineDilatation_isSMulRegular_and_map_eq_span_singleton (solution)
