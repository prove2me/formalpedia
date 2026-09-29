-- Prove2me | solution 1 for AlgebraicCurve.FunctionField.exists_ratFuncAlgHom_apply_X_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/850aeaa1-05f3-586c-bce9-70784bd1fbec

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq

open Polynomial

theorem solution {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] {g : F} (hg : g ∉ Set.range (algebraMap K F)) : ∃ φ : RatFunc K →ₐ[K] F, φ RatFunc.X = g := by

  have htr : Transcendental K g := by
    intro halg
    apply hg
    have hint : IsIntegral K g := halg.isIntegral
    have hdeg : (minpoly K g).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
    obtain ⟨a, ha⟩ := minpoly.degree_eq_one_iff.mp hdeg
    exact ⟨a, ha⟩
  have hinj : Function.Injective (Polynomial.aeval (R := K) g) :=
    transcendental_iff_injective.mp htr
  refine ⟨RatFunc.liftAlgHom (Polynomial.aeval g) ?_, ?_⟩
  · intro p hp
    simp only [Submonoid.mem_comap]
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hp))
  · rw [RatFunc.liftAlgHom_apply]
    simp

end S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq
end P2MW
export P2MW.S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq (solution)
