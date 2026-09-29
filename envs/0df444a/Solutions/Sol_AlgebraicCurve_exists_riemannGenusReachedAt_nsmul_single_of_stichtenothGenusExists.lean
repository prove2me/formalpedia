-- Prove2me | solution 1 for AlgebraicCurve.exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/76a95cca-a8c6-5f34-9d2e-722cd986e596

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists

set_option autoImplicit false
set_option maxHeartbeats 4000000

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (Q : Place K F) :
    ∃ n : ℕ, RiemannGenusReachedAt γ ((n : ℤ) • Finsupp.single Q 1) := by
  classical
  obtain ⟨n, hn⟩ :=
    exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached h Q
  refine ⟨n, ?_⟩
  have hidx := (indexOfSpecialty_eq_of_genusReached h
    ((n : ℤ) • Finsupp.single Q (1 : ℤ))).2
  rw [hn] at hidx
  have heq : Divisor.degree ((n : ℤ) • Finsupp.single Q (1 : ℤ)) -
      (ell ((n : ℤ) • Finsupp.single Q (1 : ℤ)) : ℤ) = γ - 1 := by
    push_cast at hidx ⊢
    linarith
  exact ⟨finiteDimensional_lSpace _, heq, h.isMax⟩

end S_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists
end P2MW
export P2MW.S_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists (solution)
