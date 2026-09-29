-- Prove2me | solution 1 for Algebra.isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/03042989-a44f-51e1-9e1d-7f98ffa999ab

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq

set_option autoImplicit false

theorem solution
    (Ω : Type*) [Field Ω] [IsAlgClosed Ω] (S : Type*) [CommRing S] [Algebra Ω S] [Module.Finite Ω S]
    (h : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → 𝔪 ^ 2 = 𝔪) :
    IsReduced S ∧ Module.finrank Ω S = Nat.card (S →ₐ[Ω] Ω) := by
  classical
  haveI : IsArtinianRing S := IsArtinianRing.of_finite Ω S

  have hN2 : nilradical S ^ 2 = nilradical S := by
    rw [IsArtinianRing.nilradical_pow_eq_iInf, IsArtinianRing.nilradical_eq_iInf]
    exact iInf_congr fun I => h I.asIdeal I.isMaximal
  have hNpow : ∀ n : ℕ, nilradical S ^ (n + 1) = nilradical S := by
    intro n
    induction n with
    | zero => rw [pow_one]
    | succ n ih => rw [pow_succ, ih, ← pow_two, hN2]
  have hN : nilradical S = ⊥ := by
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := S)
    rw [Submodule.zero_eq_bot] at hn
    cases n with
    | zero => rw [pow_zero, Ideal.one_eq_top] at hn; exact eq_bot_iff.mpr (le_top.trans hn.le)
    | succ n => rw [← hNpow n]; exact hn
  haveI hred : IsReduced S := nilradical_eq_bot_iff.mp hN
  refine ⟨hred, ?_⟩

  haveI : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  have hbij : ∀ I : MaximalSpectrum S, Function.Bijective (algebraMap Ω (S ⧸ I.asIdeal)) := by
    intro I
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    haveI : Module.Finite Ω (S ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ Ω I.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective Ω I.asIdeal)
    haveI : Algebra.IsIntegral Ω (S ⧸ I.asIdeal) := Algebra.IsIntegral.of_finite Ω _
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let eI : ∀ I : MaximalSpectrum S, Ω ≃ₐ[Ω] S ⧸ I.asIdeal := fun I =>
    AlgEquiv.ofBijective (Algebra.ofId Ω (S ⧸ I.asIdeal)) (hbij I)
  have hrank : Module.finrank Ω S = Fintype.card (MaximalSpectrum S) := by
    let e : S ≃ₗ[Ω] ∀ I : MaximalSpectrum S, S ⧸ I.asIdeal :=
      ((IsArtinianRing.equivPi S).toLinearEquiv.restrictScalars Ω)
    rw [e.finrank_eq, Module.finrank_pi_fintype]
    simp_rw [fun I => ((eI I).toLinearEquiv.finrank_eq).symm, Module.finrank_self]
    simp

  have hker : ∀ φ : S →ₐ[Ω] Ω, (RingHom.ker φ.toRingHom).IsMaximal := fun φ =>
    RingHom.ker_isMaximal_of_surjective φ.toRingHom
      (fun c => ⟨algebraMap Ω S c, by simp⟩)
  let F : (S →ₐ[Ω] Ω) → MaximalSpectrum S := fun φ => ⟨RingHom.ker φ.toRingHom, hker φ⟩
  have hF : Function.Bijective F := by
    constructor
    · intro φ ψ hφψ
      have hk : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom := congrArg MaximalSpectrum.asIdeal hφψ
      ext s

      have hs : s - algebraMap Ω S (φ s) ∈ RingHom.ker ψ.toRingHom := by
        rw [← hk, RingHom.mem_ker]
        simp
      rw [RingHom.mem_ker] at hs
      have : ψ s - φ s = 0 := by simpa using hs
      exact (sub_eq_zero.mp this).symm
    · intro I
      haveI : I.asIdeal.IsMaximal := I.isMaximal
      let φ : S →ₐ[Ω] Ω := (eI I).symm.toAlgHom.comp (Ideal.Quotient.mkₐ Ω I.asIdeal)
      refine ⟨φ, ?_⟩
      apply MaximalSpectrum.ext
      show RingHom.ker φ.toRingHom = I.asIdeal
      ext s
      rw [RingHom.mem_ker]
      show (eI I).symm (Ideal.Quotient.mk I.asIdeal s) = 0 ↔ s ∈ I.asIdeal
      rw [map_eq_zero_iff _ (eI I).symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  rw [hrank, ← Nat.card_eq_fintype_card, Nat.card_eq_of_bijective F hF]

end S_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq
end P2MW
export P2MW.S_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq (solution)
