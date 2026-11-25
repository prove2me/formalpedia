-- Prove2me | solution 1 for Algebra.norm_surjective_of_C1_perfectClosure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T07:58:35.610502+00:00
-- url     : https://prove2.me/submissions/2ccb36b4-3118-44ef-996c-858a55f7862d

import Mathlib
import Definitions.Def_RPLib_S4_Tsen

set_option autoImplicit false

namespace RamanujanPetersson
namespace EtGenCurveUp

open IntermediateField Polynomial Module

section Helpers

variable {F L Ω : Type*} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra L Ω] [Algebra F Ω]
  [IsScalarTower F L Ω] (E : IntermediateField F Ω) [IsPurelyInseparable F E]

/-- A separable minimal polynomial does not change over a purely inseparable extension. -/
theorem minpoly_perf_eq [Algebra.IsSeparable F L] (y : L) :
    minpoly E (algebraMap L Ω y) = (minpoly F y).map (algebraMap F E) := by
  have hsep : IsSeparable F (algebraMap L Ω y) := by
    have h := Algebra.IsSeparable.isSeparable F y
    unfold IsSeparable at h ⊢
    rwa [minpoly.algebraMap_eq (algebraMap L Ω).injective]
  rw [← minpoly.map_eq_of_isSeparable_of_isPurelyInseparable E _ hsep,
    minpoly.algebraMap_eq (algebraMap L Ω).injective]

set_option synthInstance.maxHeartbeats 400000 in
/-- The norms of `L / F` and of a degree-`[L : F]` extension `M / E` agree on `L`. -/
theorem norm_compat [IsAlgClosed Ω] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (M : IntermediateField E Ω) [FiniteDimensional E M] (hM : finrank E M = finrank F L)
    (y : L) (y' : M) (hy : (y' : Ω) = algebraMap L Ω y) :
    algebraMap F Ω (Algebra.norm F y) = algebraMap E Ω (Algebra.norm E y') := by
  have hmin : minpoly E y' = (minpoly F y).map (algebraMap F E) := by
    rw [← minpoly_perf_eq E y, ← hy]
    exact (minpoly.algebraMap_eq (algebraMap M Ω).injective y').symm
  have h1 := Algebra.norm_eq_prod_roots (K := F) Ω (x := y) (IsAlgClosed.splits _)
  have h2 := Algebra.norm_eq_prod_roots (K := E) Ω (x := y') (IsAlgClosed.splits _)
  rw [h1, h2, hmin, aroots_map]
  congr 1
  have hyi : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  have hyi' : IsIntegral E y' := Algebra.IsIntegral.isIntegral y'
  have d1 := Module.finrank_mul_finrank F F⟮y⟯ L
  have d2 := Module.finrank_mul_finrank E E⟮y'⟯ M
  have e1 : finrank F F⟮y⟯ = (minpoly F y).natDegree := adjoin.finrank hyi
  have e2 : finrank E E⟮y'⟯ = (minpoly F y).natDegree := by
    rw [adjoin.finrank hyi', hmin, natDegree_map]
  have pos : 0 < (minpoly F y).natDegree := minpoly.natDegree_pos hyi
  refine Nat.eq_of_mul_eq_mul_left pos ?_
  calc (minpoly F y).natDegree * finrank F⟮y⟯ L = finrank F L := by rw [← e1, d1]
    _ = finrank E M := hM.symm
    _ = (minpoly F y).natDegree * finrank E⟮y'⟯ M := by rw [← d2, e2]

end Helpers

/-- Norms through the perfect closure, with the `C₁` hypothesis on `perfectClosure F L̄` (Tsen's `IsC1`). -/
theorem norm_surjective_of_perfectClosure {F L : Type*} [Field F] [Field L] [Algebra F L]
    (q : ℕ) [ExpChar F q] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (hq : Nat.Coprime q (finrank F L)) (hC1 : RamanujanPetersson.Tsen.IsC1 (perfectClosure F (AlgebraicClosure L))) :
    Function.Surjective (Algebra.norm F : L → F) := by
  classical
  intro a
  have : ExpChar L q := expChar_of_injective_algebraMap (algebraMap F L).injective q
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F L
  have hαi : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hθ : IsIntegral (perfectClosure F (AlgebraicClosure L)) (algebraMap L (AlgebraicClosure L) α) :=
    (IsIntegral.algebraMap hαi).tower_top
  have : FiniteDimensional (perfectClosure F (AlgebraicClosure L))
      (perfectClosure F (AlgebraicClosure L))⟮algebraMap L (AlgebraicClosure L) α⟯ :=
    adjoin.finiteDimensional hθ
  have hM : finrank (perfectClosure F (AlgebraicClosure L))
      (perfectClosure F (AlgebraicClosure L))⟮algebraMap L (AlgebraicClosure L) α⟯ = finrank F L := by
    rw [adjoin.finrank hθ, minpoly_perf_eq _ α, natDegree_map, ← adjoin.finrank hαi, hα, finrank_top']
  obtain ⟨b, hb⟩ := hC1.norm_surjective
    (L := (perfectClosure F (AlgebraicClosure L))⟮algebraMap L (AlgebraicClosure L) α⟯)
    (algebraMap F (perfectClosure F (AlgebraicClosure L)) a)
  -- `b ^ q ^ n ∈ L`
  have hle : perfectClosure F (AlgebraicClosure L) ≤
      (perfectClosure L (AlgebraicClosure L)).restrictScalars F := by
    intro x hx
    obtain ⟨n, hn⟩ := (mem_perfectClosure_iff_pow_mem q).1 hx
    obtain ⟨c, hc⟩ := RingHom.mem_range.1 hn
    refine (mem_restrictScalars F).2 ((mem_perfectClosure_iff_pow_mem q).2 ⟨n, ⟨algebraMap F L c, ?_⟩⟩)
    rw [← hc, ← IsScalarTower.algebraMap_apply]
  have hMle : (perfectClosure F (AlgebraicClosure L))⟮algebraMap L (AlgebraicClosure L) α⟯ ≤
      extendScalars hle := by
    rw [adjoin_simple_le_iff, mem_extendScalars, mem_restrictScalars]
    exact (mem_perfectClosure_iff_pow_mem q).2 ⟨0, ⟨α, by simp⟩⟩
  have hbL : (b : AlgebraicClosure L) ∈ perfectClosure L (AlgebraicClosure L) :=
    (mem_restrictScalars F).1 ((mem_extendScalars hle).1 (hMle b.2))
  obtain ⟨n, hn⟩ := (mem_perfectClosure_iff_pow_mem q).1 hbL
  obtain ⟨y, hy⟩ := RingHom.mem_range.1 hn
  have hN : algebraMap F (AlgebraicClosure L) (Algebra.norm F y) =
      algebraMap F (AlgebraicClosure L) (a ^ q ^ n) := by
    rw [norm_compat _ _ hM y (b ^ q ^ n) (by rw [hy]; exact SubmonoidClass.coe_pow b _), map_pow, hb,
      ← map_pow, ← IsScalarTower.algebraMap_apply]
  have hNy : Algebra.norm F y = a ^ q ^ n := (algebraMap F (AlgebraicClosure L)).injective hN
  have hcop : Nat.Coprime (q ^ n) (finrank F L) := Nat.Coprime.pow_left n hq
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha, Algebra.norm_zero]⟩
  rcases Nat.lt_or_ge 1 (finrank F L) with hl | hl
  · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hl
    obtain ⟨j, hqm⟩ : ∃ j, q ^ n * m = finrank F L * j + 1 :=
      ⟨_, by rw [← hm]; exact (Nat.div_add_mod _ _).symm⟩
    refine ⟨y ^ m * (algebraMap F L a⁻¹) ^ j, ?_⟩
    rw [map_mul, map_pow, map_pow, hNy, Algebra.norm_algebraMap, ← pow_mul, ← pow_mul, hqm, inv_pow,
      pow_succ, mul_comm (a ^ _) a, mul_inv_cancel_right₀ (pow_ne_zero _ ha)]
  · have h1 : finrank F L = 1 := by have := Module.finrank_pos (R := F) (M := L); omega
    exact ⟨algebraMap F L a, by rw [Algebra.norm_algebraMap, h1, pow_one]⟩

end EtGenCurveUp
end RamanujanPetersson

theorem solution
    (F : Type*) [Field F] (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (q : ℕ) [ExpChar F q] (hq : Nat.Coprime q (Module.finrank F L))
    (hC1 : ∀ (n : ℕ) (f : MvPolynomial (Fin n) (perfectClosure F (AlgebraicClosure L))),
      f.totalDegree < n → MvPolynomial.constantCoeff f = 0 →
        ∃ x : Fin n → perfectClosure F (AlgebraicClosure L), x ≠ 0 ∧ MvPolynomial.eval x f = 0) :
    Function.Surjective (Algebra.norm F : L → F) := by
  exact RamanujanPetersson.EtGenCurveUp.norm_surjective_of_perfectClosure (F := F) (L := L) q hq hC1
