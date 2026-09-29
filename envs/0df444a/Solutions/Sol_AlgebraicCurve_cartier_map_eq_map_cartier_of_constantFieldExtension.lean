-- Prove2me | solution 1 for AlgebraicCurve.cartier_map_eq_map_cartier_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2afb2c1a-bdd0-57d4-96c2-1bca0b0ba2f7

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_exists_D_ne_zero
import Theorems.Thm_AlgebraicCurve_existsUnique_pDigits_of_D_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_cartier_map_eq_map_cartier_of_constantFieldExtension

set_option autoImplicit false

namespace CartierBC

open KaehlerDifferential

theorem C_pow_smul_D_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (p : ℕ) [CharP F p]
    (C : Ω[F⁄K] →+ Ω[F⁄K]) (hker : ∀ f : F, C (D K F f) = 0) (t : F) {i : ℕ} (hi : i + 1 < p) :
    C (t ^ i • D K F t) = 0 := by
  have h1 : D K F (t ^ (i + 1)) = (i + 1) • (t ^ i • D K F t) := by
    rw [Derivation.leibniz_pow, Nat.add_sub_cancel]
  have h2 : (((i + 1 : ℕ) : F)) • C (t ^ i • D K F t) = 0 := by
    rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← h1, hker]
  have hne : ((i + 1 : ℕ) : F) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff F p] at h
    exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos i) hi h
  calc C (t ^ i • D K F t)
      = ((i + 1 : ℕ) : F)⁻¹ • ((((i + 1 : ℕ) : F)) • C (t ^ i • D K F t)) := (inv_smul_smul₀ hne _).symm
    _ = 0 := by rw [h2, smul_zero]

theorem C_digits_smul_D {K F : Type*} [Field K] [Field F] [Algebra K F] (p : ℕ) [hp : Fact p.Prime]
    [CharP F p] (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • D K F f) = D K F f)
    (t : F) (a : Fin p → F) :
    C ((∑ i : Fin p, a i ^ p * t ^ (i : ℕ)) • D K F t)
      = a ⟨p - 1, Nat.sub_lt hp.out.pos Nat.one_pos⟩ • D K F t := by
  rw [Finset.sum_smul, map_sum]
  have key : ∀ i : Fin p, C ((a i ^ p * t ^ (i : ℕ)) • D K F t)
      = if (i : ℕ) = p - 1 then a i • D K F t else 0 := by
    intro i
    rw [mul_smul, hsemi]
    split_ifs with h
    · rw [h, hlog]
    · rw [C_pow_smul_D_eq_zero p C hker t (i := (i : ℕ)) (by have := i.isLt; omega), smul_zero]
  simp_rw [key]
  rw [Finset.sum_eq_single (⟨p - 1, Nat.sub_lt hp.out.pos Nat.one_pos⟩ : Fin p)]
  · rw [if_pos rfl]
  · intro i _ hne
    rw [if_neg]
    intro h
    exact hne (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem exists_eq_smul_D {K F : Type*} [Field K] [Field F] [Algebra K F] (p : ℕ) [CharP F p] (t : F)
    (hdig : ∀ g : F, ∃ a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ)) (ω : Ω[F⁄K]) :
    ∃ g : F, ω = g • D K F t := by
  have htop : (⊤ : Submodule F (Ω[F⁄K])) ≤ Submodule.span F {D K F t} := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    obtain ⟨a, rfl⟩ := hdig g
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (nsmul_mem (Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self _)) _)) ?_
    rw [← Nat.cast_smul_eq_nsmul F p, CharP.cast_eq_zero, zero_smul, smul_zero]
    exact Submodule.zero_mem _
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp (htop (Submodule.mem_top (x := ω)))
  exact ⟨g, hg.symm⟩

end CartierBC

open CartierBC in
theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [SMulCommClass K' F F']
    [PerfectField K] [AlgebraicCurve.IsCurveOver K F]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (C' : Ω[F'⁄K'] →+ Ω[F'⁄K'])
    (hsemi' : ∀ (f : F') (ω : Ω[F'⁄K']), C' (f ^ p • ω) = f • C' ω)
    (hker' : ∀ f : F', C' (KaehlerDifferential.D K' F' f) = 0)
    (hlog' : ∀ f : F', C' (f ^ (p - 1) • KaehlerDifferential.D K' F' f) = KaehlerDifferential.D K' F' f) :
    ∀ ω : Ω[F⁄K], C' (KaehlerDifferential.map K K' F F' ω) = KaehlerDifferential.map K K' F F' (C ω) := by
  intro ω
  obtain ⟨x, -, hxfin⟩ := hfg
  haveI := hxfin
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  haveI : CharP F' p := charP_of_injective_algebraMap (algebraMap K F').injective p
  obtain ⟨t, hdt⟩ := AlgebraicCurve.exists_D_ne_zero (K := K) (F := F)
  have hdig : ∀ g : F, ∃ a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) :=
    fun g => (AlgebraicCurve.existsUnique_pDigits_of_D_ne_zero (K := K) p x hdt g).exists
  obtain ⟨g, rfl⟩ := exists_eq_smul_D (K := K) p t hdig ω
  obtain ⟨a, rfl⟩ := hdig g

  rw [C_digits_smul_D p C hsemi hker hlog t a]

  have hsm : ∀ (s : F) (m : Ω[F'⁄K']), s • m = algebraMap F F' s • m :=
    fun s m => (algebraMap_smul F' s m).symm
  rw [LinearMap.map_smul, LinearMap.map_smul, KaehlerDifferential.map_D, hsm, hsm]
  simp only [map_sum, map_mul, map_pow]

  exact C_digits_smul_D p C' hsemi' hker' hlog' (algebraMap F F' t) (fun i => algebraMap F F' (a i))

end S_AlgebraicCurve_cartier_map_eq_map_cartier_of_constantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_cartier_map_eq_map_cartier_of_constantFieldExtension (solution)
