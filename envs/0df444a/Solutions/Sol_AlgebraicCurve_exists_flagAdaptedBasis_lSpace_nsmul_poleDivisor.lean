-- Prove2me | solution 1 for AlgebraicCurve.exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1b6844c8-c289-520d-b070-92efcf99a127

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor
import Theorems.Thm_AlgebraicCurve_lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
import Theorems.Thm_AlgebraicCurve_linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor

set_option autoImplicit false
set_option maxHeartbeats 3200000

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (hell0 : ell (0 : Divisor K F) = 1)
    (M₀ d g₀ : ℕ) (hd : 1 ≤ d)
    (hell : ∀ N, M₀ ≤ N → (ell (N • D) : ℤ) = N * d + 1 - g₀) :
    ∃ (d' : ℕ) (y : Fin d' → F) (e : Fin d' → ℕ),
      (∀ M : ℕ, (LSpace (M • D) : Submodule K F)
        ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ}) ∧
      LinearIndependent K (fun p : Fin d' × ℕ => x ^ p.2 * y p.1) ∧
      (∀ σ, y σ ∈ LSpace ((e σ) • D)) := by

  obtain ⟨d', y, e, hle, hy, hspanFin, hLIat⟩ :=
    exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor x hx D hD hFD hell0 (M₀ + 1)

  have hspanAll : ∀ M : ℕ, (LSpace (M • D) : Submodule K F)
      ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ} := by
    intro M
    induction M using Nat.strong_induction_on with
    | _ M ih =>
      rcases le_or_gt M (M₀ + 1) with hM | hM
      · exact hspanFin M hM
      · obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
        have hstep := lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
          x D hD hFD M₀ d g₀ hell M' (by omega)
        refine hstep.trans (sup_le ((ih M' (by omega)).trans (Submodule.span_mono ?_)) ?_)
        · rintro z ⟨σ, j, hje, rfl⟩; exact ⟨σ, j, by omega, rfl⟩
        · rw [Submodule.map_le_iff_le_comap]
          refine (ih M' (by omega)).trans (Submodule.span_le.mpr ?_)
          rintro z ⟨σ, j, hje, rfl⟩
          exact Submodule.mem_comap.mpr (Submodule.subset_span
            ⟨σ, j + 1, by omega, by simp [LinearMap.mulLeft_apply, ← mul_assoc, ← pow_succ']⟩)

  exact ⟨d', y, e, hspanAll,
    linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq
      x D hD hFD M₀ d g₀ hell y e hle hy hspanAll hLIat,
    hy⟩

end S_AlgebraicCurve_exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor
end P2MW
export P2MW.S_AlgebraicCurve_exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor (solution)
