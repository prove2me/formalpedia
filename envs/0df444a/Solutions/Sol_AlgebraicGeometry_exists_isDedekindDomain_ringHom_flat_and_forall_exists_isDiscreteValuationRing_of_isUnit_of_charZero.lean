-- Prove2me | solution 1 for AlgebraicGeometry.exists_isDedekindDomain_ringHom_flat_and_forall_exists_isDiscreteValuationRing_of_isUnit_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/eb26c48d-dd5e-5152-b94b-416540ba723b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isDedekindDomain_ringHom_flat_and_forall_exists_isDiscreteValuationRing_of_isUnit_of_charZero

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace ASM21
namespace E4

theorem away_lift (n : ℕ) (hn0 : (n : ℤ) ≠ 0) (T : Type) [CommRing T] [IsDomain T] [CharZero T] (hT : IsUnit ((n : ℕ) : T)) :
    ∃ i : Localization.Away (n : ℤ) →+* T, Function.Injective i ∧
      (∀ z : ℤ, i (algebraMap ℤ (Localization.Away (n : ℤ)) z) = (z : T)) ∧
      (letI := i.toAlgebra; Module.Flat (Localization.Away (n : ℤ)) T) := by
  classical
  have hM : Submonoid.powers (n : ℤ) ≤ nonZeroDivisors ℤ := powers_le_nonZeroDivisors_of_noZeroDivisors hn0
  haveI : IsDomain (Localization.Away (n : ℤ)) := IsLocalization.isDomain_localization hM
  haveI : IsDedekindDomain (Localization.Away (n : ℤ)) := IsLocalization.isDedekindDomain ℤ hM _
  have hnT : IsUnit (Int.castRingHom T (n : ℤ)) := by simpa using hT
  let i : Localization.Away (n : ℤ) →+* T := Localization.awayLift (Int.castRingHom T) (n : ℤ) hnT
  have hi_alg : ∀ z : ℤ, i (algebraMap ℤ _ z) = (z : T) := fun z => by
    simp [i, Localization.awayLift, IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hinj : Function.Injective i := by
    intro x y hxy
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (n : ℤ)) x
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (n : ℤ)) y
    rw [IsLocalization.mk'_eq_iff_eq]
    have ha := congrArg (fun w => w * i (algebraMap ℤ _ s) * i (algebraMap ℤ _ t)) hxy
    simp only at ha
    have e1 : i (IsLocalization.mk' _ a s) * i (algebraMap ℤ _ ↑s) = i (algebraMap ℤ _ a) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    have e2 : i (IsLocalization.mk' _ b t) * i (algebraMap ℤ _ ↑t) = i (algebraMap ℤ _ b) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    have : i (algebraMap ℤ _ a) * i (algebraMap ℤ _ ↑t) = i (algebraMap ℤ _ b) * i (algebraMap ℤ _ ↑s) := by
      calc i (algebraMap ℤ _ a) * i (algebraMap ℤ _ ↑t)
          = i (IsLocalization.mk' _ a s) * i (algebraMap ℤ _ ↑s) * i (algebraMap ℤ _ ↑t) := by rw [e1]
        _ = i (IsLocalization.mk' _ b t) * i (algebraMap ℤ _ ↑t) * i (algebraMap ℤ _ ↑s) := by rw [ha]; ring
        _ = i (algebraMap ℤ _ b) * i (algebraMap ℤ _ ↑s) := by rw [e2]
    rw [hi_alg, hi_alg, hi_alg, hi_alg] at this
    have : ((a * (t : ℤ) : ℤ) : T) = ((b * (s : ℤ) : ℤ) : T) := by push_cast; exact this
    have hab := Int.cast_injective this
    congr 1
    linear_combination hab
  refine ⟨i, hinj, hi_alg, ?_⟩
  letI : Algebra (Localization.Away (n : ℤ)) T := i.toAlgebra
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
  change (a : Localization.Away (n : ℤ)) • x = 0 at hax
  rw [Algebra.smul_def, mul_eq_zero] at hax
  rcases hax with h | h
  · exfalso
    have : (a : Localization.Away (n : ℤ)) = 0 := hinj (by rw [map_zero]; exact h)
    exact nonZeroDivisors.ne_zero ha this
  · exact h

theorem not_isUnit_of_prime_not_dvd (n : ℕ) (hn0 : (n : ℤ) ≠ 0) (p : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ n) :
    ¬ IsUnit ((p : ℕ) : Localization.Away (n : ℤ)) := by
  classical
  have hM : Submonoid.powers (n : ℤ) ≤ nonZeroDivisors ℤ := powers_le_nonZeroDivisors_of_noZeroDivisors hn0
  rintro ⟨u, hu⟩
  obtain ⟨bs, hb⟩ := IsLocalization.mk'_surjective (Submonoid.powers (n : ℤ)) ((u⁻¹ : (Localization.Away (n : ℤ))ˣ) : Localization.Away (n : ℤ))
  dsimp only at hb
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 bs.2.2

  have hpu : (algebraMap ℤ (Localization.Away (n : ℤ))) (p : ℤ) = (u : Localization.Away (n : ℤ)) := by rw [hu]; simp
  have hspec := IsLocalization.mk'_spec (Localization.Away (n : ℤ)) bs.1 bs.2
  have hone : (algebraMap ℤ (Localization.Away (n : ℤ))) (p : ℤ) * IsLocalization.mk' _ bs.1 bs.2 = 1 := by
    rw [hpu, hb, Units.mul_inv]
  have h1 : (algebraMap ℤ (Localization.Away (n : ℤ)) (p * bs.1)) = algebraMap ℤ _ ((n : ℤ) ^ k) := by
    calc (algebraMap ℤ (Localization.Away (n : ℤ)) (p * bs.1))
        = (algebraMap ℤ _ (p : ℤ)) * (IsLocalization.mk' _ bs.1 bs.2 * algebraMap ℤ _ (bs.2 : ℤ)) := by rw [map_mul, hspec]
      _ = algebraMap ℤ _ (bs.2 : ℤ) := by rw [← mul_assoc, hone, one_mul]
      _ = algebraMap ℤ _ ((n : ℤ) ^ k) := by rw [hk]
  have h2 : (p : ℤ) * bs.1 = (n : ℤ) ^ k := IsLocalization.injective (Localization.Away (n : ℤ)) hM h1
  have h3 : (p : ℤ) ∣ (n : ℤ) ^ k := ⟨bs.1, h2.symm⟩
  have h4 : (p : ℤ) ∣ (n : ℤ) := (Int.prime_iff_natAbs_prime.2 (by simpa using hp)).dvd_of_dvd_pow h3
  exact hpn (by exact_mod_cast h4)

end ASM21.E4

namespace ASM21
namespace E4

theorem witt_witness (n : ℕ) (hn0 : (n : ℤ) ≠ 0) (p : ℕ) [hp : Fact p.Prime] (hpn : ¬ p ∣ n) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : IsAlgClosed (IsLocalRing.ResidueField W))
      (_ : Algebra (Localization.Away (n : ℤ)) W),
      Module.Flat (Localization.Away (n : ℤ)) W ∧
        (IsLocalRing.maximalIdeal W).comap (algebraMap (Localization.Away (n : ℤ)) W) =
          Ideal.map (algebraMap ℤ (Localization.Away (n : ℤ))) (Ideal.span {(p : ℤ)}) := by
  classical
  let k := AlgebraicClosure (ZMod p)
  let W := WittVector p k

  haveI : CharZero W := by
    have hf : Function.Injective ((WittVector.map (algebraMap (ZMod p) k)).comp (WittVector.equiv p).symm.toRingHom) := by
      apply (WittVector.map_injective _ (algebraMap (ZMod p) k).injective).comp
      exact (WittVector.equiv p).symm.injective
    exact charZero_of_injective_ringHom hf

  have hnk : ((n : ℕ) : k) ≠ 0 := fun h => hpn ((CharP.cast_eq_zero_iff k p n).1 h)
  have hnW : IsUnit ((n : ℕ) : W) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [← WittVector.constantCoeff_apply, map_natCast]
    exact hnk
  obtain ⟨iW, hinjW, hiW, hflatW⟩ := away_lift n hn0 W hnW
  letI algW : Algebra (Localization.Away (n : ℤ)) W := iW.toAlgebra
  have hmax : IsLocalRing.maximalIdeal W = Ideal.span {(p : W)} := (WittVector.irreducible p).maximalIdeal_eq
  have hadic : IsAdicComplete (IsLocalRing.maximalIdeal W) W := by
    rw [hmax]; exact WittVector.isAdicCompleteIdealSpanP
  have halg : IsAlgClosed (IsLocalRing.ResidueField W) := by
    let e : IsLocalRing.ResidueField W ≃+* k := (Ideal.quotEquivOfEq hmax).trans WittVector.quotientPEquiv
    exact IsAlgClosed.of_ringEquiv k _ e.symm
  refine ⟨W, inferInstance, inferInstance, inferInstance, hadic, halg, algW, hflatW, ?_⟩

  set P' := (IsLocalRing.maximalIdeal W).comap (algebraMap (Localization.Away (n : ℤ)) W) with hP'
  have hP'ne : P' ≠ ⊤ := Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal W).ne_top
  have hunder : Ideal.under ℤ P' = Ideal.span {(p : ℤ)} := by
    symm
    have hpmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime (by simpa using hp.out.ne_zero)
        ((Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp.out))
    refine hpmax.eq_of_le (Ideal.comap_ne_top _ hP'ne) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap (Localization.Away (n : ℤ)) W (algebraMap ℤ (Localization.Away (n : ℤ)) (p : ℤ)) ∈ IsLocalRing.maximalIdeal W
    rw [show algebraMap (Localization.Away (n : ℤ)) W = iW from rfl, hiW, hmax]
    exact_mod_cast Ideal.mem_span_singleton_self (p : W)
  rw [← hunder]
  exact (IsLocalization.map_under (Submonoid.powers (n : ℤ)) (Localization.Away (n : ℤ)) P').symm

end ASM21.E4

theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (n : ℕ) (hn : IsUnit ((n : ℕ) : 𝒪)) :
    ∃ (B₀ : Type) (_ : CommRing B₀) (_ : IsDedekindDomain B₀) (i : B₀ →+* 𝒪),
      Flat (Spec.map (CommRingCat.ofHom i)) ∧ IsUnit ((n : ℕ) : B₀) ∧
      (∀ 𝔭 : Ideal B₀, 𝔭.IsMaximal →
        ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
          (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : IsAlgClosed (IsLocalRing.ResidueField W))
          (_ : Algebra B₀ W), Module.Flat B₀ W ∧ (IsLocalRing.maximalIdeal W).comap (algebraMap B₀ W) = 𝔭) := by
  classical
  have hn0' : n ≠ 0 := by rintro rfl; simp at hn
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn0'
  have hM : Submonoid.powers (n : ℤ) ≤ nonZeroDivisors ℤ := powers_le_nonZeroDivisors_of_noZeroDivisors hn0
  haveI : IsDomain (Localization.Away (n : ℤ)) := IsLocalization.isDomain_localization hM
  haveI : IsDedekindDomain (Localization.Away (n : ℤ)) := IsLocalization.isDedekindDomain ℤ hM _
  obtain ⟨i, hinj, hi, hflat⟩ := ASM21.E4.away_lift n hn0 𝒪 hn
  have hnB : IsUnit ((n : ℕ) : Localization.Away (n : ℤ)) := by
    have : ((n : ℕ) : Localization.Away (n : ℤ)) = algebraMap ℤ _ (n : ℤ) := by simp
    rw [this]; exact IsLocalization.Away.algebraMap_isUnit (n : ℤ)
  refine ⟨Localization.Away (n : ℤ), inferInstance, inferInstance, i, ?_, hnB, ?_⟩
  · rw [HasRingHomProperty.Spec_iff (P := @Flat)]; exact hflat
  intro 𝔭 h𝔭

  let q : Ideal ℤ := Ideal.under ℤ 𝔭
  have hqprime : q.IsPrime := Ideal.IsPrime.under ℤ 𝔭
  have h𝔭q : Ideal.map (algebraMap ℤ (Localization.Away (n : ℤ))) q = 𝔭 := IsLocalization.map_under (Submonoid.powers (n : ℤ)) (Localization.Away (n : ℤ)) 𝔭

  have hqne : q ≠ ⊥ := by
    intro hq0
    have h𝔭0 : 𝔭 = ⊥ := by rw [← h𝔭q, hq0, Ideal.map_bot]
    obtain ⟨p₀, hp₀n, hp₀⟩ := Nat.exists_infinite_primes (n + 1)
    have hp₀dvd : ¬ p₀ ∣ n := fun h => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0') h; omega
    have hne : Ideal.span {((p₀ : ℕ) : Localization.Away (n : ℤ))} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      have : ((p₀ : ℕ) : Localization.Away (n : ℤ)) = algebraMap ℤ _ (p₀ : ℤ) := by simp
      rw [this, ← map_zero (algebraMap ℤ (Localization.Away (n : ℤ)))]
      intro h
      have := IsLocalization.injective (Localization.Away (n : ℤ)) hM h
      exact hp₀.ne_zero (by exact_mod_cast this)
    by_cases htop : Ideal.span {((p₀ : ℕ) : Localization.Away (n : ℤ))} = ⊤
    · exact ASM21.E4.not_isUnit_of_prime_not_dvd n hn0 p₀ hp₀ hp₀dvd (Ideal.span_singleton_eq_top.1 htop)
    · exact hne ((h𝔭0 ▸ h𝔭).eq_of_le htop bot_le).symm

  obtain ⟨g, hg⟩ : ∃ g : ℤ, q = Ideal.span {g} := ⟨_, (Ideal.span_singleton_generator q).symm⟩
  have hg0 : g ≠ 0 := fun h => hqne (by rw [hg, h, Ideal.span_singleton_eq_bot])
  have hgprime : Prime g := (Ideal.span_singleton_prime hg0).1 (hg ▸ hqprime)
  set p : ℕ := g.natAbs with hpdef
  have hp : p.Prime := Int.prime_iff_natAbs_prime.1 hgprime
  have hqp : q = Ideal.span {(p : ℤ)} := by rw [hg, hpdef, Int.span_natAbs]
  have hpn : ¬ p ∣ n := by
    intro hdvd
    have hpu : IsUnit ((p : ℕ) : Localization.Away (n : ℤ)) :=
      isUnit_of_dvd_unit (Nat.cast_dvd_cast hdvd) hnB
    have hpmem : ((p : ℕ) : Localization.Away (n : ℤ)) ∈ 𝔭 := by
      have : (p : ℤ) ∈ q := by rw [hqp]; exact Ideal.mem_span_singleton_self _
      have := Ideal.mem_comap.1 this
      simpa using this
    exact h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem _ hpmem hpu)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨W, _, _, _, hadic, halg, algW, hflatW, hcomap⟩ := ASM21.E4.witt_witness n hn0 p hpn
  refine ⟨W, inferInstance, inferInstance, inferInstance, hadic, halg, algW, hflatW, ?_⟩
  rw [hcomap, ← hqp, h𝔭q]

end S_AlgebraicGeometry_exists_isDedekindDomain_ringHom_flat_and_forall_exists_isDiscreteValuationRing_of_isUnit_of_charZero
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isDedekindDomain_ringHom_flat_and_forall_exists_isDiscreteValuationRing_of_isUnit_of_charZero (solution)
