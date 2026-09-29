-- Prove2me | solution 1 for AlgebraicCurve.exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/10cda7f3-4bf3-5818-bb45-60d77230d22f

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace ALGAux

theorem dimensionLEOne_of_height_maximalIdeal_le_one (S : Type*) [CommRing S] [IsDomain S]
    [IsLocalRing S] (h : (maximalIdeal S).height ≤ 1) : Ring.DimensionLEOne S := by
  refine ⟨fun {p} hp hpp => ?_⟩
  rcases (IsLocalRing.le_maximalIdeal hpp.ne_top).lt_or_eq with hlt | heq
  · exfalso
    have h1 : p.height < (1 : ℕ) :=
      (Ideal.height_le_iff (p := maximalIdeal S) (n := 1)).mp (by exact_mod_cast h) p hpp hlt
    have h0 : p.height = 0 := by
      have h1' : p.height < 1 := by exact_mod_cast h1
      exact ENat.lt_one_iff_eq_zero.mp h1'
    have hmin := Ideal.height_eq_zero_iff.mp h0
    rw [IsDomain.minimalPrimes_eq_singleton_bot] at hmin
    exact hp hmin
  · exact heq ▸ IsLocalRing.maximalIdeal.isMaximal S

theorem exists_place_of_isDedekindDomain (L F : Type*) [Field L] [Field F] [Algebra L F]
    (R : Subring F) [IsLocalRing R] [IsDedekindDomain R] [IsFractionRing R F]
    (hL : ∀ a : L, algebraMap L F a ∈ R) (hR : R ≠ ⊤) :
    ∃ P : Place L F, P.toValuationSubring.toSubring = R := by
  haveI hPIR : IsPrincipalIdealRing R := inferInstance
  haveI : ValuationRing R := inferInstance
  have hmem : ∀ x : F, x ∈ R ∨ x⁻¹ ∈ R := fun x => by
    rcases ValuationRing.isInteger_or_isInteger R x with ⟨y, hy⟩ | ⟨y, hy⟩
    · left; rw [← hy]; exact y.2
    · right; rw [← hy]; exact y.2
  let V : ValuationSubring F := ⟨R, hmem⟩
  refine ⟨⟨V, hL, ?_, hPIR⟩, rfl⟩
  intro hV
  apply hR
  refine Subring.eq_top_iff'  _ |>.mpr fun x => ?_
  have hx : x ∈ V := hV.symm ▸ ValuationSubring.mem_top x
  exact hx

end ALGAux

open ALGAux in
theorem solution
    {L F : Type*} [Field L] [IsAlgClosed L] [Field F] [Algebra L F] [IsCurveOver L F]
    (R : Subring F) [IsLocalRing ↥R] [IsNoetherianRing ↥R] [IsFractionRing ↥R F]
    (hn : IsIntegrallyClosedIn ↥R F)
    (hL : ∀ a : L, algebraMap L F a ∈ R) (hR : R ≠ ⊤) :
    ∃ P : Place L F, P.toValuationSubring.toSubring = R := by
  classical

  letI algLR : Algebra L R := ((algebraMap L F).codRestrict R hL).toAlgebra
  haveI : IsScalarTower L R F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsIntegrallyClosed R := (isIntegrallyClosed_iff_isIntegrallyClosedIn F).mpr hn

  have hnf : ¬IsField (R : Type _) := by
    intro hf
    apply hR
    have hbij := IsField.localization_map_bijective (M := nonZeroDivisors R) (Rₘ := F)
      (flip nonZeroDivisors.ne_zero rfl : (0 : R) ∉ nonZeroDivisors R) hf
    refine Subring.eq_top_iff' _ |>.mpr fun x => ?_
    obtain ⟨r, hr⟩ := hbij.2 x
    rw [← hr]
    exact r.2
  have hm : maximalIdeal R ≠ ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq (R := R)).not.mp hnf
  obtain ⟨f, hfm, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm

  have hspan : Ideal.span {f} ≤ maximalIdeal R := (Ideal.span_singleton_le_iff_mem _).mpr hfm
  obtain ⟨q, hqmin, hqle⟩ := Ideal.exists_minimalPrimes_le hspan
  haveI hqp : q.IsPrime := hqmin.1.1
  have hqh : q.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {f}) q hqmin
  have hfq : f ∈ q := hqmin.1.2 (Ideal.mem_span_singleton_self f)
  have hqne : q ≠ ⊥ := fun h => hf0 (by rw [h] at hfq; exact (Submodule.mem_bot _).mp hfq)

  let A : Subalgebra R F :=
    Localization.subalgebra.ofField F q.primeCompl q.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime A q :=
    Localization.subalgebra.isLocalization_ofField F q.primeCompl q.primeCompl_le_nonZeroDivisors
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A q
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing q.primeCompl A inferInstance
  haveI : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isLocalization A q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hKA : ringKrullDim A = q.height := IsLocalization.AtPrime.ringKrullDim_eq_height q A
  have hmA : (maximalIdeal A).height ≤ 1 := by
    have h2 : ((maximalIdeal A).height : WithBot ℕ∞) = q.height :=
      (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)).trans hKA
    rw [WithBot.coe_inj] at h2
    exact h2 ▸ hqh
  haveI : Ring.DimensionLEOne A := dimensionLEOne_of_height_maximalIdeal_le_one A hmA
  haveI : IsDedekindDomain A :=
    (isDedekindDomain_iff A F).mpr ⟨inferInstance, ‹_›, ‹_›, (isIntegrallyClosed_iff F).mp ‹_›⟩

  letI algLA : Algebra L A := ((algebraMap R A).comp (algebraMap L R)).toAlgebra
  haveI : IsScalarTower L A F := IsScalarTower.of_algebraMap_eq (fun c => by
    show algebraMap A F ((algebraMap R A) (algebraMap L R c)) = algebraMap L F c
    rw [← IsScalarTower.algebraMap_apply R A F, ← IsScalarTower.algebraMap_apply L R F])
  have hmaxA : maximalIdeal A ≠ ⊥ := by
    intro h
    apply hqne
    rw [← IsLocalization.AtPrime.under_maximalIdeal A q, h]
    exact Ideal.comap_bot_of_injective (algebraMap R A)
      (IsLocalization.injective A q.primeCompl_le_nonZeroDivisors)

  let w : IsDedekindDomain.HeightOneSpectrum A := ⟨maximalIdeal A, inferInstance, hmaxA⟩
  let P₀ : Place L F := Place.ofHeightOneSpectrum (K := L) (R := A) w
  have hAV : ∀ a : A, algebraMap A F a ∈ P₀.toValuationSubring.toSubring := fun a => by
    show algebraMap A F a ∈ (w.valuation F).valuationSubring
    rw [Valuation.mem_valuationSubring_iff]
    exact w.valuation_le_one a
  let χ : A →+* P₀.toValuationSubring :=
    (algebraMap A F).codRestrict P₀.toValuationSubring.toSubring hAV
  let ψ : R →+* P₀.toValuationSubring := χ.comp (algebraMap R A)

  haveI : Module.Finite L P₀.ResidueField := IsCurveOver.finiteResidue P₀
  haveI : Algebra.IsIntegral L P₀.ResidueField := Algebra.IsIntegral.of_finite L _
  have hsurj : Function.Surjective (algebraMap L P₀.ResidueField) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := P₀.ResidueField)).2
  have hψL : ∀ c : L, ψ (algebraMap L R c) = algebraMap L P₀.toValuationSubring c := fun c => by
    apply Subtype.ext
    show algebraMap A F (algebraMap R A (algebraMap L R c)) = algebraMap L F c
    rw [← IsScalarTower.algebraMap_apply R A F, ← IsScalarTower.algebraMap_apply L R F]
  have hresL : ∀ c : L, IsLocalRing.residue _ (algebraMap L P₀.toValuationSubring c)
      = algebraMap L P₀.ResidueField c := fun c =>
    (IsScalarTower.algebraMap_apply L P₀.toValuationSubring P₀.ResidueField c).symm

  have key : maximalIdeal R ≤ q := by
    intro r hr
    by_contra hrq
    have hu : IsUnit (ψ r) := (IsLocalization.map_units A (⟨r, hrq⟩ : q.primeCompl)).map χ
    obtain ⟨c, hc⟩ := hsurj (IsLocalRing.residue _ (ψ r))
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero, eq_comm, IsLocalRing.residue_eq_zero_iff] at hc
      exact (IsLocalRing.mem_maximalIdeal _).mp hc hu
    have hd : r - algebraMap L R c ∈ maximalIdeal R := by
      have h1 : ψ (r - algebraMap L R c) ∈ maximalIdeal P₀.toValuationSubring := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, hψL, hresL, hc, sub_self]
      have h2 : ¬IsUnit (r - algebraMap L R c) := fun h =>
        (IsLocalRing.mem_maximalIdeal _).mp h1 (h.map ψ)
      exact (IsLocalRing.mem_maximalIdeal _).mpr h2
    have hcm : algebraMap L R c ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hr hd
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).mp hcm ((hc0.isUnit).map (algebraMap L R))
  have hqm : q = maximalIdeal R := le_antisymm hqle key

  have hRh : (maximalIdeal R).height ≤ 1 := hqm ▸ hqh
  haveI : Ring.DimensionLEOne R := dimensionLEOne_of_height_maximalIdeal_le_one R hRh
  haveI : IsDedekindDomain R :=
    (isDedekindDomain_iff R F).mpr ⟨inferInstance, ‹_›, ‹_›, (isIntegrallyClosed_iff F).mp ‹_›⟩
  exact exists_place_of_isDedekindDomain L F R hL hR

end S_AlgebraicCurve_exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing
end P2MW
export P2MW.S_AlgebraicCurve_exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing (solution)
