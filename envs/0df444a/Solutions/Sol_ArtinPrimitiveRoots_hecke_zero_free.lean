-- Prove2me | solution 1 for ArtinPrimitiveRoots.hecke_zero_free
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T10:51:35.913224+00:00
-- url     : https://prove2.me/submissions/b31afd78-70d7-4c1c-a306-eb36550b1027
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Theorems.Thm_ArtinPrimitiveRoots_exists_differentiableOn_eq_heckeLSeries
import Theorems.Thm_ArtinPrimitiveRoots_heckeLSeries_euler_package_of_le
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_principalCorrection_regular
import Theorems.Thm_ArtinPrimitiveRoots_ne_zero_of_norm_principalMellinOf_le
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_norm_principalMellin_le

section
namespace ArtinPrimitiveRoots

open NumberField

/-- Enlarging a nonzero modulus so that every prime of norm `≤ N₀` divides it. -/
theorem T12R_exists_smallPrimesDvd (F : Type*) [Field F] [NumberField F] (N₀ : ℕ)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ 𝔪' : Ideal (𝓞 F), 𝔪' ≠ ⊥ ∧ 𝔪' ≤ 𝔪 ∧ SmallPrimesDvd N₀ 𝔪' := by
  refine ⟨𝔪 * Ideal.span {((Nat.factorial N₀ : ℕ) : 𝓞 F)}, ?_, Ideal.mul_le_left, ?_⟩
  · rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
    refine ⟨h𝔪, ?_⟩
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Nat.factorial_pos N₀).ne'
  · intro P hP hP0 hN
    refine le_trans Ideal.mul_le_right ?_
    rw [Ideal.span_singleton_le_iff_mem]
    have h0 : 0 < Ideal.absNorm P := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
    obtain ⟨k, hk⟩ := Nat.dvd_factorial h0 hN
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem P)

/-- The primes containing a nonzero ideal form a finite set. -/
theorem T12R_finite_primes_ge (F : Type*) [Field F] [NumberField F]
    (𝔪' : Ideal (𝓞 F)) (h𝔪' : 𝔪' ≠ ⊥) (q : Ideal (𝓞 F) → Prop) :
    {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪' ≤ P ∧ q P}.Finite := by
  refine (Ideal.finite_setOfPred_absNorm_le (Ideal.absNorm 𝔪')).subset ?_
  intro P ⟨_, _, hle, _⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
    (Ideal.absNorm_dvd_absNorm_of_le hle)

/-- An Euler factor `(1 − c N^{−s})⁻¹` with `‖c‖ ≤ 1`, `N ≥ 2` is holomorphic and nonzero on
`Re s > 0`. -/
theorem T12R_eulerFactor (c : ℂ) (hc : ‖c‖ ≤ 1) (N : ℕ) (hN : 2 ≤ N) (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun s : ℂ => (1 - c * (N : ℂ) ^ (-s))⁻¹) s ∧
      (1 - c * (N : ℂ) ^ (-s))⁻¹ ≠ 0 := by
  have hne : 1 - c * (N : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have h1 : c * (N : ℂ) ^ (-s) = 1 := by linear_combination -h
    have hlt : ‖c * (N : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
      have : (N : ℝ) ^ (-s.re) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < N)) (by linarith)
      calc ‖c‖ * (N : ℝ) ^ (-s.re) ≤ 1 * (N : ℝ) ^ (-s.re) := by gcongr
        _ < 1 := by linarith
    rw [h1, norm_one] at hlt
    exact lt_irrefl _ hlt
  refine ⟨?_, inv_ne_zero hne⟩
  refine DifferentiableAt.inv ?_ hne
  refine (differentiableAt_const _).sub ((differentiableAt_const _).mul ?_)
  exact (differentiableAt_id.neg).const_cpow (Or.inl (by exact_mod_cast (by omega : N ≠ 0)))

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open NumberField
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) :
    χ.ZeroFreeRight (1 - 1 / 10 ^ 6) := by
  -- Step 1: an embedding.
  obtain ⟨ι⟩ := (inferInstance : Nonempty (F →+* ℂ))
  -- Steps 2–3: cutoff and enlarged modulus.
  obtain ⟨N₃, hT3⟩ := exists_cutoff_principalCorrection_regular n hn0 hn F ι
  obtain ⟨N₅, hT5⟩ := exists_cutoff_norm_principalMellin_le n hn0 hn F ι
  obtain ⟨𝔪', h𝔪', hle, hsm⟩ := T12R_exists_smallPrimesDvd F (max N₃ N₅) 𝔪 h𝔪
  have hsm3 : SmallPrimesDvd N₃ 𝔪' := fun P hP hP0 hN =>
    hsm P hP hP0 (hN.trans (le_max_left _ _))
  have hsm5 : SmallPrimesDvd N₅ 𝔪' := fun P hP hP0 hN =>
    hsm P hP hP0 (hN.trans (le_max_right _ _))
  -- Steps 4–8.
  obtain ⟨hχ1, -, -, χ', -, hEul⟩ := heckeLSeries_euler_package_of_le F 𝔪 𝔪' h𝔪' hle χ
  obtain ⟨-, hL1', ⟨B, hLb'⟩, -⟩ := heckeLSeries_euler_package_of_le F 𝔪' 𝔪' h𝔪' le_rfl χ'
  obtain ⟨g', hg'd, hg'eq⟩ := exists_differentiableOn_eq_heckeLSeries F 𝔪' h𝔪' χ'
  obtain ⟨hHd, hH0, BH, hHb⟩ := hT3 𝔪' hsm3 χ'
  obtain ⟨C, Z₀, hf⟩ := hT5 𝔪' h𝔪' hsm5 χ'
  have hδ : (998 / 1000 : ℝ) < 1 - 1 / 20000 := by norm_num
  -- Step 9: T4.
  have hT4 := ne_zero_of_norm_principalMellinOf_le g' (χ'.principalCorrection ι) (1 / 20000)
    (hg'd.mono fun s hs => hs.2)
    (fun s hs => by rw [hg'eq s hs]; exact hL1' s hs)
    ⟨B, fun s hs => by rw [hg'eq s (by linarith)]; exact hLb' s hs⟩
    (hHd.mono fun s (hs : 1 - 1 / 20000 < s.re) => show (998 / 1000 : ℝ) < s.re by linarith)
    (fun s hs => hH0 s (by linarith))
    ⟨BH, fun s hs => hHb s (by linarith)⟩
    ⟨C, Z₀, fun Z hZ => by
      have hcongr : principalMellinOf (χ'.principalCorrection ι) g' Z =
          χ'.principalMellin ι Z := by
        unfold HeckeChar.principalMellin principalMellinOf
        congr 2
        funext τ
        rw [hg'eq]
        simp
      rw [hcongr]
      exact hf Z hZ⟩
  -- Step 10: glue back the finitely many Euler factors.
  have hS := T12R_finite_primes_ge F 𝔪' h𝔪' (fun P => P ⊔ 𝔪 = ⊤)
  have hEP : ∀ s : ℂ, (∏ᶠ (P : Ideal (𝓞 F)) (_ : P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪' ≤ P ∧ P ⊔ 𝔪 = ⊤),
      (1 - χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s))⁻¹) =
      ∏ P ∈ hS.toFinset, (1 - χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s))⁻¹ := fun s =>
    finprod_cond_eq_prod_of_cond_iff _ (fun {P} _ => by simp)
  have hN2 : ∀ P ∈ hS.toFinset, 2 ≤ Ideal.absNorm P := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    obtain ⟨hPp, hP0, -, -⟩ := hP
    have h0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hPp.ne_top
    omega
  have hfac : ∀ P ∈ hS.toFinset, ∀ s : ℂ, 0 < s.re →
      DifferentiableAt ℂ (fun s : ℂ => (1 - χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s))⁻¹) s ∧
      (1 - χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s))⁻¹ ≠ 0 := fun P hP s hs =>
    T12R_eulerFactor _ (hχ1 P) _ (hN2 P hP) s hs
  have hσ : (1 - 1 / 20000 : ℝ) < 1 - 1 / 10 ^ 6 := by norm_num
  refine ⟨fun s => g' s *
      ∏ P ∈ hS.toFinset, (1 - χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s))⁻¹, ?_, ?_, ?_⟩
  · intro s hs
    have hre : 0 < s.re := by linarith [hs.1]
    refine DifferentiableWithinAt.mul ((hg'd s hs.2).mono fun z hz => hz.2) ?_
    exact (DifferentiableAt.fun_finsetProd fun P hP => (hfac P hP s hre).1).differentiableWithinAt
  · intro s hs
    simp only
    rw [hEul s hs, hg'eq s hs, hEP]
  · intro s hs hs1
    exact mul_ne_zero (hT4 s (by linarith) hs1)
      (Finset.prod_ne_zero_iff.mpr fun P hP => (hfac P hP s (by linarith)).2)
end
