-- Prove2me | solution 1 for AlgebraicCurve.RROpens.exists_effective_sub_add_smul_single_mem_principal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b6e7f449-492f-5204-b4de-7b68c3940958

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RROpens_exists_effective_sub_add_smul_single_mem_principal

set_option autoImplicit false

universe u v

open AlgebraicCurve Module

theorem solution {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] (g : ℕ) (Kc : Divisor K F)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) (hP : P.deg = 1) (A : Divisor K F) (hA : Divisor.degree A = 0) :
    ∃ E : Divisor K F, (∀ v, 0 ≤ E v) ∧
      E - (A + (g : ℤ) • Finsupp.single P 1) ∈ Divisor.principal (K := K) (F := F) := by
  set D : Divisor K F := A + (g : ℤ) • Finsupp.single P 1 with hD

  have hdeg : Divisor.degree D = g := by
    rw [hD, map_add, map_zsmul, Divisor.degree_single, hA, hP]
    simp

  have hpos : 0 < finrank K (LSpace D) := by
    have h := hRR D
    rw [hdeg] at h
    have h0 : (0 : ℤ) ≤ (ell (Kc - D) : ℤ) := Int.natCast_nonneg _
    have h1 : (1 : ℤ) ≤ (ell D : ℤ) := by linarith
    have h2 : 1 ≤ ell D := by exact_mod_cast h1
    exact h2

  have hne : LSpace D ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨f, hfD, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hord : ∀ v : Place K F, -D v ≤ v.ord f := (mem_lSpace_iff_ord.mp hfD).resolve_left hf0

  obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine ⟨D + Df, fun v => ?_, ?_⟩
  · rw [Finsupp.add_apply, hDf v]
    linarith [hord v]
  · rw [add_sub_cancel_left]
    exact ⟨f, hf0, hDf⟩

#print axioms solution

end S_AlgebraicCurve_RROpens_exists_effective_sub_add_smul_single_mem_principal
end P2MW
export P2MW.S_AlgebraicCurve_RROpens_exists_effective_sub_add_smul_single_mem_principal (solution)
