-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LocalizationAdicPatch_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13LocalizationAdicPatch_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:36:10.692562+00:00
-- url     : https://prove2.me/theorems/e709b91b-226a-4b9a-8d6f-0153f65ec884
-- title:
--   FLT.Assumptions.MazurProof.N13LocalizationAdicPatch source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13LocalizationAdicPatch

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13LocalizationAdicPatch
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13PrimitiveVerticalPresentation_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

An algebraic patching lemma for the remaining generic infinity comparison:
equality away from t plus approximation to every t-adic order implies ideal
equality. Its proof uses the module form of Krull intersection, not a claimed
faithfulness of the Laurent branches. Producing the approximation hypothesis
from the actual branch maps is a separate remaining step.
-/

namespace MazurProof.N13LocalizationAdicPatch

noncomputable section

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

theorem eq_zero_of_nilpotent_and_adically_small
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (t : R) (x : M)
    (hnil : ∃ n : ℕ, t ^ n • x = 0)
    (hsmall : x ∈ ⨅ n : ℕ, Ideal.span ({t} : Set R) ^ n • (⊤ : Submodule R M)) :
    x = 0 := by
  obtain ⟨n, hn⟩ := hnil
  obtain ⟨a, ha⟩ :=
    ((Ideal.span ({t} : Set R)).mem_iInf_smul_pow_eq_bot_iff x).mp hsmall
  have hat : t ∣ (a : R) := Ideal.mem_span_singleton.mp a.property
  obtain ⟨b, hab⟩ := hat
  have hpow : ∀ k : ℕ, (a : R) ^ k • x = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_smul, ih, ha]
  calc
    x = (a : R) ^ n • x := (hpow n).symm
    _ = (t * b) ^ n • x := by rw [hab]
    _ = b ^ n • (t ^ n • x) := by rw [mul_pow, mul_comm, mul_smul]
    _ = 0 := by rw [hn, smul_zero]

/-- A finite module quotient cannot retain an element that both dies after
inverting t and is approximable by zero to every t-adic order. -/
theorem ideal_le_of_localization_le_of_approximations
    {T : Type*} [CommRing T] [Algebra R T]
    (t : R) [IsLocalization (Submonoid.powers t) T]
    (I J : Ideal R)
    (hAway : Ideal.map (algebraMap R T) I ≤ Ideal.map (algebraMap R T) J)
    (hApprox : ∀ x : R, x ∈ I → ∀ n : ℕ,
      ∃ y : R, x - t ^ n * y ∈ J) : I ≤ J := by
  intro x hx
  let q : R →+* R ⧸ J := Ideal.Quotient.mk J
  have hnil : ∃ n : ℕ, t ^ n • q x = 0 := by
    have hm := hAway (Ideal.mem_map_of_mem (algebraMap R T) hx)
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers t)] at hm
    obtain ⟨s, hs, hsx⟩ := hm
    obtain ⟨n, rfl⟩ := hs
    refine ⟨n, ?_⟩
    have hh : q (t ^ n * x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hsx
    simpa [q, Algebra.smul_def] using hh
  have hsmall : q x ∈ ⨅ n : ℕ,
      Ideal.span ({t} : Set R) ^ n • (⊤ : Submodule R (R ⧸ J)) := by
    refine (Submodule.mem_iInf _).mpr fun n => ?_
    obtain ⟨y, hy⟩ := hApprox x hx n
    have hh : q (x - t ^ n * y) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
    have hq : q x = t ^ n • q y := by
      rw [map_sub, map_mul] at hh
      simpa [q, Algebra.smul_def] using sub_eq_zero.mp hh
    rw [hq]
    apply Submodule.smul_mem_smul
    · rw [Ideal.span_singleton_pow]
      exact Ideal.subset_span (Set.mem_singleton (t ^ n))
    · exact Submodule.mem_top
  have hxzero := eq_zero_of_nilpotent_and_adically_small t (q x) hnil hsmall
  exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero

theorem ideal_eq_of_localization_eq_of_approximations
    {T : Type*} [CommRing T] [Algebra R T]
    (t : R) [IsLocalization (Submonoid.powers t) T]
    (I J : Ideal R)
    (hAway : Ideal.map (algebraMap R T) I = Ideal.map (algebraMap R T) J)
    (hIJ : ∀ x : R, x ∈ I → ∀ n : ℕ, ∃ y : R, x - t ^ n * y ∈ J)
    (hJI : ∀ x : R, x ∈ J → ∀ n : ℕ, ∃ y : R, x - t ^ n * y ∈ I) :
    I = J := by
  exact le_antisymm
    (ideal_le_of_localization_le_of_approximations t I J hAway.le hIJ)
    (ideal_le_of_localization_le_of_approximations t J I hAway.symm.le hJI)

end
end MazurProof.N13LocalizationAdicPatch


