-- Prove2me | solution 1 for Algebra.FormallyUnramified.ext_of_isHausdorff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5af3e3b5-9247-5e0f-be05-4c4988ad3284

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallyUnramified_ext_of_isHausdorff

theorem solution (R A B : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.FormallyUnramified R A] (I : Ideal B) [IsHausdorff I B] (f g : A →ₐ[R] B)
    (h : (Ideal.Quotient.mkₐ R I).comp f = (Ideal.Quotient.mkₐ R I).comp g) : f = g := by
  apply AlgHom.ext
  intro a
  have key : ∀ n : ℕ, f a - g a ∈ I ^ n := by
    intro n
    rcases n with _ | n
    · simp
    · let J : Ideal (B ⧸ I ^ (n+1)) := I.map (Ideal.Quotient.mk (I ^ (n+1)))
      have hJb : J ^ (n+1) = ⊥ := by
        rw [← Ideal.map_pow, Ideal.map_quotient_self]
      have hJ : IsNilpotent J := ⟨n+1, hJb.trans Submodule.zero_eq_bot.symm⟩
      have hn : (Ideal.Quotient.mkₐ R (I ^ (n+1))).comp f
          = (Ideal.Quotient.mkₐ R (I ^ (n+1))).comp g := by
        apply Algebra.FormallyUnramified.lift_unique J hJ
        apply AlgHom.ext
        intro x
        have hx := AlgHom.congr_fun h x
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at hx ⊢
        rw [Ideal.Quotient.eq] at hx ⊢
        rw [← map_sub]
        exact Ideal.mem_map_of_mem _ hx
      have := AlgHom.congr_fun hn a
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
      exact (Ideal.Quotient.eq).mp this
  refine sub_eq_zero.mp (IsHausdorff.haus' (I := I) (M := B) (f a - g a) fun n => ?_)
  rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
  exact key n

end S_Algebra_FormallyUnramified_ext_of_isHausdorff
end P2MW
export P2MW.S_Algebra_FormallyUnramified_ext_of_isHausdorff (solution)
