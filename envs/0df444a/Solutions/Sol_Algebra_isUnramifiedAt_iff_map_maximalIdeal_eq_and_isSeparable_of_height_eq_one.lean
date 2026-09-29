-- Prove2me | solution 1 for Algebra.isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b4ca6492-fb66-5161-b343-19e5a42e57e1

import Mathlib
import Theorems.Thm_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one

set_option autoImplicit false

namespace E9M5c

theorem height_under_eq_one
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (S : Type*) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
    (Q : Ideal S) [Q.IsPrime] (hQ : Q.height = 1) : (Q.under R).height = 1 := by
  apply le_antisymm
  · obtain ⟨l, hlast, hlen⟩ := Ideal.exists_ltSeries_length_eq_height (Q.under R)
    haveI : Q.LiesOver l.last.asIdeal := by rw [hlast]; infer_instance
    obtain ⟨L, hLlen, hLlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q
    have h1 : (L.length : ℕ∞) ≤ Order.height L.last := Order.length_le_height_last
    rw [hLlast, ← PrimeSpectrum.height_eq_orderHeight, hLlen] at h1
    calc (Q.under R).height = l.length := by exact_mod_cast hlen.symm
      _ ≤ Q.height := h1
      _ = 1 := hQ
  · have hQ0 : Q ≠ ⊥ := by
      rintro rfl; rw [Ideal.height_bot] at hQ; exact zero_ne_one hQ
    obtain ⟨q, hqQ, hq0⟩ := Q.ne_bot_iff.mp hQ0
    have hne : Q.under R ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem hq0 hqQ (Algebra.IsIntegral.isIntegral q)
    have hlt : (⊥ : Ideal R) < Q.under R := bot_lt_iff_ne_bot.mpr hne
    have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [Ideal.height_bot, zero_add] at this
    exact this

end E9M5c

theorem solution
    {O C : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    [CommRing C] [IsDomain C] [IsNoetherianRing C] [IsIntegrallyClosed C]
    [Algebra O C] [Module.Finite O C] [NoZeroSMulDivisors O C]
    (P : Ideal C) [P.IsPrime] (hP : P.height = 1)
    [Algebra (Localization.AtPrime (P.under O)) (Localization.AtPrime P)]
    [Localization.AtPrime.IsLiesOverAlgebra (P.under O) P] :
    (P.under O).height = 1 ∧
    IsDiscreteValuationRing (Localization.AtPrime (P.under O)) ∧
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
    (Algebra.IsUnramifiedAt O P ↔
      Ideal.map (algebraMap O (Localization.AtPrime P)) (P.under O) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P) ∧
      Algebra.IsSeparable (P.under O).ResidueField P.ResidueField) := by
  haveI : FaithfulSMul O C := inferInstance
  have h1 : (P.under O).height = 1 := E9M5c.height_under_eq_one O C P hP
  refine ⟨h1, Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one (P.under O) h1,
    Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one P hP, ?_⟩
  rw [Algebra.isUnramifiedAt_iff_map_eq O (P.under O) P]
  exact and_comm

end S_Algebra_isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one
end P2MW
export P2MW.S_Algebra_isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one (solution)
