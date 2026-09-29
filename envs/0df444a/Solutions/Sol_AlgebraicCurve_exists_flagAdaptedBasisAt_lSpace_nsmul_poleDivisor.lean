-- Prove2me | solution 1 for AlgebraicCurve.exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d0421133-ab4c-56af-a959-1ce268292324

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor

set_option autoImplicit false
set_option maxHeartbeats 8000000

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (hell0 : ell (0 : Divisor K F) = 1) (M₁ : ℕ) :
    ∃ (d' : ℕ) (y : Fin d' → F) (e : Fin d' → ℕ),
      (∀ σ, e σ ≤ M₁) ∧
      (∀ σ, y σ ∈ LSpace ((e σ) • D)) ∧
      (∀ M ≤ M₁, (LSpace (M • D) : Submodule K F)
        ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ}) ∧
      (∀ M ≤ M₁, LinearIndependent K
        (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ M} => x ^ p.val.2 * y p.val.1)) := by
  classical
  induction M₁ with
  | zero =>
    haveI : FiniteDimensional K ↥(LSpace (0 • D) : Submodule K F) := hFD 0
    have hfr0 : Module.finrank K ↥(LSpace (0 • D) : Submodule K F) = 1 := by
      have h : ell ((0:ℕ) • D) = 1 := by rw [zero_smul]; exact hell0
      exact h
    have hne : (LSpace (0 • D) : Submodule K F) ≠ ⊥ := by
      intro h; rw [h] at hfr0; simp at hfr0
    obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hLv : (LSpace (0 • D) : Submodule K F) = Submodule.span K {v} := by
      refine (Submodule.eq_of_le_of_finrank_le
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvmem))
        (by rw [finrank_span_singleton hvne, hfr0])).symm
    refine ⟨1, fun _ => v, fun _ => 0, fun _ => le_refl 0, ?_, ?_, ?_⟩
    · intro σ; simpa using hvmem
    · intro M hM; obtain rfl : M = 0 := Nat.le_zero.mp hM
      rw [hLv]; refine Submodule.span_mono ?_
      rintro w rfl; exact ⟨0, 0, le_refl 0, by simp⟩
    · intro M hM; obtain rfl : M = 0 := Nat.le_zero.mp hM
      letI hU : Unique {p : Fin 1 × ℕ // p.2 + (fun _ => 0) p.1 ≤ 0} :=
        ⟨⟨⟨(0, 0), by simp⟩⟩, by
          rintro ⟨⟨a, j⟩, ha⟩; simp only [add_zero] at ha
          exact Subtype.ext (Prod.ext (Subsingleton.elim a 0) (Nat.le_zero.mp ha))⟩
      refine linearIndependent_unique_iff.mpr ?_
      have : (default : {p : Fin 1 × ℕ // p.2 + (fun _ => 0) p.1 ≤ 0}).val.2 = 0 := rfl
      simp only [this, pow_zero, one_mul]
      exact hvne
  | succ M₁ ih =>
    obtain ⟨d', y, e, hle', hy', hspan', hLI'⟩ := ih
    exact exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ
      x hx D hD hFD hell0 M₁ y e hle' hy' hspan' hLI'

end S_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor
end P2MW
export P2MW.S_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor (solution)
