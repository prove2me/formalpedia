-- Prove2me | solution 1 for Algebra.isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/d30f63cc-3cab-5d66-b865-c8d4a2272ac6

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one

set_option autoImplicit false

universe u

open IsLocalRing

namespace L5hAux

theorem exists_valuationSubring_of_height_eq_one
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Q : Ideal R) [Q.IsPrime] (hQ : Q.height = 1) :
    ∃ V : ValuationSubring K,
      (∀ x : K, x ∈ V ↔ ∃ r s : R, s ∉ Q ∧ x * algebraMap R K s = algebraMap R K r) ∧
      IsPrincipalIdealRing V ∧
      (∀ r : R, algebraMap R K r ∈ V) ∧
      (∀ r : R, algebraMap R K r ∈ V.nonunits ↔ r ∈ Q) := by
  classical

  set S := Localization.AtPrime Q with hS
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    rw [Ideal.height_bot] at hQ
    exact zero_ne_one hQ
  have hle : Q.primeCompl ≤ nonZeroDivisors R := Q.primeCompl_le_nonZeroDivisors
  haveI : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S Q.primeCompl hle
  have hmne : maximalIdeal S ≠ ⊥ := by
    intro h
    apply hQ0
    have := IsLocalization.AtPrime.comap_maximalIdeal S Q
    rw [h] at this
    rw [← this]
    exact Ideal.comap_bot_of_injective _ (IsLocalization.injective S hle)
  have hnf : ¬ IsField S := (IsLocalRing.isField_iff_maximalIdeal_eq).not.mpr hmne
  haveI : Ring.KrullDimLE 1 S := ⟨by
    change ringKrullDim S ≤ 1
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q S, hQ]
    exact le_rfl⟩
  have hexu : ∃! P : Ideal S, P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨maximalIdeal S, ⟨hmne, inferInstance⟩, fun P hP => ?_⟩
    haveI := hP.2
    exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal_of_ne_bot hP.2 hP.1)
  have h03 := (IsDiscreteValuationRing.TFAE S hnf).out 0 3
  haveI hdvr : IsDiscreteValuationRing S := h03.mpr (And.intro inferInstance hexu)

  letI algSK : Algebra S K := (IsLocalization.lift (M := Q.primeCompl) (g := algebraMap R K)
    (fun s => IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
      (nonZeroDivisors.ne_zero (hle s.2))))).toAlgebra
  haveI : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.lift_eq _ r).symm
  haveI : IsFractionRing S K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl S K
  have hinjSK : Function.Injective (algebraMap S K) := IsFractionRing.injective S K

  let V : ValuationSubring K :=
    { (algebraMap S K).range with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger S x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact Or.inl ⟨y, hy⟩
        · exact Or.inr ⟨y, hy⟩ }
  have hVmem : ∀ x : K, x ∈ V ↔ ∃ y : S, algebraMap S K y = x := fun x => Iff.rfl

  let e : S ≃+* V := RingEquiv.ofBijective
    ((algebraMap S K).codRestrict V.toSubring fun y => ⟨y, rfl⟩)
    ⟨fun a b h => hinjSK (congrArg Subtype.val h), fun ⟨x, y, hy⟩ => ⟨y, Subtype.ext hy⟩⟩
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hVmem]
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y
      refine ⟨r, s, s.2, ?_⟩
      rw [IsScalarTower.algebraMap_apply R S K, IsScalarTower.algebraMap_apply R S K, ← map_mul,
        IsLocalization.mk'_spec]
    · rintro ⟨r, s, hs, hx⟩
      refine ⟨IsLocalization.mk' S r (⟨s, hs⟩ : Q.primeCompl), ?_⟩
      have hs0 : algebraMap R K s ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr fun h => hs (h ▸ Q.zero_mem)
      apply mul_right_cancel₀ hs0
      rw [hx, IsScalarTower.algebraMap_apply R S K s, ← map_mul, IsLocalization.mk'_spec,
        ← IsScalarTower.algebraMap_apply]
  · exact IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  · intro r
    exact ⟨algebraMap R S r, (IsScalarTower.algebraMap_apply R S K r).symm⟩
  · intro r
    have hmem : algebraMap R K r ∈ V := ⟨algebraMap R S r, (IsScalarTower.algebraMap_apply R S K r).symm⟩
    have hcoe : algebraMap R K r = ((⟨algebraMap R K r, hmem⟩ : V) : K) := rfl
    rw [hcoe, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have he : e (algebraMap R S r) = ⟨algebraMap R K r, hmem⟩ :=
      Subtype.ext (IsScalarTower.algebraMap_apply R S K r).symm
    rw [← he]
    constructor
    · intro hnu
      by_contra hrQ
      exact hnu ((IsLocalization.map_units S (⟨r, hrQ⟩ : Q.primeCompl)).map e)
    · intro hrQ hu
      have hu' : IsUnit (algebraMap R S r) := by
        simpa using hu.map e.symm
      exact ((IsLocalization.AtPrime.isUnit_to_map_iff S Q r).mp hu') hrQ

theorem exists_place_of_height_eq_one
    (L : Type) [Field L] (F : Type) [Field F] [Algebra L F]
    (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Algebra R F] [IsFractionRing R F]
    (Q : Ideal R) [Q.IsPrime] (hQ : Q.height = 1)
    (hL : ∀ c : L, ∃ a b : R, b ∉ Q ∧ algebraMap L F c * algebraMap R F b = algebraMap R F a) :
    ∃ w : AlgebraicCurve.Place L F,
      (∀ x : F, x ∈ w.toValuationSubring ↔ ∃ r s : R, s ∉ Q ∧ x * algebraMap R F s = algebraMap R F r) ∧
      (∀ r : R, algebraMap R F r ∈ w.toValuationSubring) ∧
      (∀ r : R, algebraMap R F r ∈ w.toValuationSubring.nonunits ↔ r ∈ Q) ∧
      (∀ r : R, 0 ≤ w.ord (algebraMap R F r)) ∧
      (∀ r : R, r ≠ 0 → (0 < w.ord (algebraMap R F r) ↔ r ∈ Q)) := by
  classical
  obtain ⟨V, hV, hPIR, hRV, hnu⟩ := exists_valuationSubring_of_height_eq_one R F Q hQ
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    rw [Ideal.height_bot] at hQ
    exact zero_ne_one hQ

  have hLV : ∀ c : L, algebraMap L F c ∈ V := by
    intro c
    obtain ⟨a, b, hb, hab⟩ := hL c
    have hbV : algebraMap R F b ∈ V := hRV b
    have hbu : IsUnit (⟨algebraMap R F b, hbV⟩ : V) := by
      by_contra hnu'
      have : algebraMap R F b ∈ V.nonunits := by
        have hcoe : algebraMap R F b = ((⟨algebraMap R F b, hbV⟩ : V) : F) := rfl
        rw [hcoe, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal]
        exact hnu'
      exact hb ((hnu b).mp this)
    have hb0 : algebraMap R F b ≠ 0 := by
      intro h0
      apply hbu.ne_zero
      exact Subtype.ext h0
    have hc : algebraMap L F c = algebraMap R F a * (algebraMap R F b)⁻¹ := by
      rw [← hab, mul_inv_cancel_right₀ hb0]
    rw [hc]
    have hval : V.valuation (algebraMap R F b) = 1 := (V.valuation_eq_one_iff ⟨_, hbV⟩).mp hbu
    have hinv : (algebraMap R F b)⁻¹ ∈ V := (V.valuation_le_one_iff _).mp (by rw [map_inv₀, hval, inv_one])
    exact mul_mem (hRV a) hinv

  have hVtop : V ≠ ⊤ := by
    obtain ⟨q, hqQ, hq0⟩ := Q.ne_bot_iff.mp hQ0
    intro htop
    have hqnu : algebraMap R F q ∈ V.nonunits := (hnu q).mpr hqQ
    rw [ValuationSubring.mem_nonunits_iff_or] at hqnu
    rcases hqnu with h0 | hninv
    · exact hq0 ((map_eq_zero_iff _ (IsFractionRing.injective R F)).mp h0)
    · exact hninv (htop ▸ Subring.mem_top _)
  let w : AlgebraicCurve.Place L F :=
    { toValuationSubring := V
      algebraMap_mem' := hLV
      ne_top' := hVtop
      isPrincipalIdealRing' := hPIR }
  have hwV : w.toValuationSubring = V := rfl

  have hord0 : ∀ r : R, 0 ≤ w.ord (algebraMap R F r) := by
    intro r
    rcases eq_or_ne r 0 with rfl | hr
    · simp
    have hr0 : algebraMap R F r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr
    by_cases hu : IsUnit (⟨algebraMap R F r, hRV r⟩ : w.toValuationSubring)
    · obtain ⟨u, hu⟩ := hu
      have := w.ord_coe_unit u
      rw [hu] at this
      exact this.symm.le
    · have hmax : (⟨algebraMap R F r, hRV r⟩ : w.toValuationSubring) ∈
          IsLocalRing.maximalIdeal w.toValuationSubring := by
        rwa [IsLocalRing.mem_maximalIdeal]
      exact ((w.mem_maximalIdeal_iff_ord_pos hr0 (hRV r)).mp hmax).le
  have hordQ : ∀ r : R, r ≠ 0 → (0 < w.ord (algebraMap R F r) ↔ r ∈ Q) := by
    intro r hr
    have hr0 : algebraMap R F r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr
    rw [← w.mem_maximalIdeal_iff_ord_pos hr0 (hRV r), ← ValuationSubring.coe_mem_nonunits_iff]
    exact hnu r
  exact ⟨w, hV, hRV, hnu, hord0, hordQ⟩

theorem height_under_eq_one
    (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
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

theorem isAlgebraic_residueField
    (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P]
    [Algebra (Localization.AtPrime P) (Localization.AtPrime Q)] [Localization.AtPrime.IsLiesOverAlgebra P Q] :
    Algebra.IsAlgebraic (IsLocalRing.ResidueField (Localization.AtPrime P))
      (IsLocalRing.ResidueField (Localization.AtPrime Q)) := by
  classical
  have hcomp : (algebraMap (IsLocalRing.ResidueField (Localization.AtPrime P))
      (IsLocalRing.ResidueField (Localization.AtPrime Q))).comp
        ((IsLocalRing.residue (Localization.AtPrime P)).comp (algebraMap R (Localization.AtPrime P))) =
      ((IsLocalRing.residue (Localization.AtPrime Q)).comp (algebraMap S (Localization.AtPrime Q))).comp
        (algebraMap R S) := by
    ext r
    simp only [RingHom.comp_apply]
    change IsLocalRing.ResidueField.map _ (IsLocalRing.residue _ _) = _
    rw [IsLocalRing.ResidueField.map_residue, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S]
  have hint : ∀ a : S, IsIntegral (IsLocalRing.ResidueField (Localization.AtPrime P))
      (IsLocalRing.residue (Localization.AtPrime Q) (algebraMap S (Localization.AtPrime Q) a)) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := R) a).map_of_comp_eq _ _ hcomp
  refine ⟨fun x => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y

  have ht : IsUnit (algebraMap S (Localization.AtPrime Q) t) := IsLocalization.map_units _ t
  have ht0 : IsLocalRing.residue (Localization.AtPrime Q) (algebraMap S _ t) ≠ 0 := by
    rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact ht
  have hmk : IsLocalRing.residue (Localization.AtPrime Q) (IsLocalization.mk' (Localization.AtPrime Q) a t) =
      IsLocalRing.residue _ (algebraMap S _ a) * (IsLocalRing.residue _ (algebraMap S _ t))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ ht0, ← map_mul, IsLocalization.mk'_spec]
  rw [hmk]
  exact (hint a).isAlgebraic.mul (hint t).isAlgebraic.inv

theorem isUnramifiedAt_of_map_le
    (R S : Type) [CommRing R] [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S]
    [Algebra.EssFiniteType R S]
    (Q : Ideal S) [Q.IsPrime]
    (h0 : ∀ n : ℕ, n ≠ 0 → (n : R) ∉ Q.under R)
    (key : Q.map (algebraMap S (Localization.AtPrime Q)) ≤
      (Q.under R).map (algebraMap R (Localization.AtPrime Q))) :
    Algebra.IsUnramifiedAt R Q := by
  classical
  letI := Localization.AtPrime.algebraOfLiesOver (Q.under R) Q
  haveI : IsScalarTower R (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map, ← IsScalarTower.algebraMap_apply]
  have hmap : (IsLocalRing.maximalIdeal (Localization.AtPrime (Q.under R))).map
      (algebraMap _ (Localization.AtPrime Q)) = IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q),
      ← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [IsScalarTower.algebraMap_eq R S (Localization.AtPrime Q), ← Ideal.map_map]
      exact Ideal.map_mono Ideal.map_comap_le
    · exact key
  haveI : Algebra.EssFiniteType S (Localization.AtPrime Q) := Algebra.EssFiniteType.of_isLocalization _ Q.primeCompl
  haveI : Algebra.EssFiniteType R (Localization.AtPrime Q) := Algebra.EssFiniteType.comp R S (Localization.AtPrime Q)
  haveI : Algebra.EssFiniteType (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q) :=
    Algebra.EssFiniteType.of_comp R _ _
  haveI : CharZero (IsLocalRing.ResidueField (Localization.AtPrime (Q.under R))) := by
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra hn0
    have hu : IsUnit (algebraMap R (Localization.AtPrime (Q.under R)) (n : R)) :=
      IsLocalization.map_units _ (⟨_, h0 n hn0⟩ : (Q.under R).primeCompl)
    have hres : IsLocalRing.residue _ (algebraMap R (Localization.AtPrime (Q.under R)) (n : R)) = (n : _) := by
      simp only [map_natCast]
    rw [hn, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hres
    exact hres hu
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField (Localization.AtPrime (Q.under R)))
      (IsLocalRing.ResidueField (Localization.AtPrime Q)) := isAlgebraic_residueField R S (Q.under R) Q
  have hFU : Algebra.FormallyUnramified (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q) :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmap
  haveI : Algebra.FormallyUnramified R (Localization.AtPrime (Q.under R)) :=
    Algebra.FormallyUnramified.of_isLocalization (Q.under R).primeCompl
  exact Algebra.FormallyUnramified.comp R (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q)

theorem mem_of_ord_nonneg {L F : Type} [Field L] [Field F] [Algebra L F] (w : AlgebraicCurve.Place L F)
    {x : F} (hx : x ≠ 0) (h : 0 ≤ w.ord x) : x ∈ w.toValuationSubring := by
  by_contra hxn
  rcases w.toValuationSubring.mem_or_inv_mem x with hmem | hinv
  · exact hxn hmem
  · have hnu : ¬ IsUnit (⟨x⁻¹, hinv⟩ : w.toValuationSubring) := by
      intro hu
      apply hxn
      have hval : w.toValuationSubring.valuation x⁻¹ = 1 :=
        (w.toValuationSubring.valuation_eq_one_iff ⟨_, hinv⟩).mp hu
      refine (w.toValuationSubring.valuation_le_one_iff _).mp ?_
      rw [← inv_inv x, map_inv₀, hval, inv_one]
    have hpos := (w.mem_maximalIdeal_iff_ord_pos (inv_ne_zero hx) hinv).mp
      (by rwa [IsLocalRing.mem_maximalIdeal])
    rw [w.ord_inv] at hpos
    omega

open AlgebraicCurve in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem isUnramifiedAt_of_height_eq_one_of_not_mem_of_ramificationIndexAlong_eq_one
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (F : Type) [Field F] [Algebra L F] [Algebra A F] [IsScalarTower A L F]
    (F' : Type) [Field F'] [Algebra L F'] [Algebra A F'] [IsScalarTower A L F']
    (φ : F' →ₐ[L] F)
    (B : Type) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Algebra B F] [IsScalarTower A B F]
    [IsFractionRing B F]
    (B' : Type) [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B'] [Algebra A B'] [Algebra B' F']
    [IsScalarTower A B' F'] [IsFractionRing B' F']
    [Algebra B' B] [IsScalarTower A B' B] [Module.Finite B' B]
    (hι : ∀ x : B', algebraMap B F (algebraMap B' B x) = φ (algebraMap B' F' x))
    (hint : φ.toRingHom.IsIntegral)
    (jB : B)
    (he : ∀ w : AlgebraicCurve.Place L F, 0 ≤ w.ord (algebraMap B F jB) →
      AlgebraicCurve.Place.ramificationIndexAlong φ w = 1)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (Q : Ideal B) [Q.IsPrime] (hQ1 : Q.height = 1)
    (hϖQ : algebraMap A B ϖ ∉ Q) :
    Algebra.IsUnramifiedAt B' Q := by
  classical
  haveI : IsNoetherianRing B :=
    isNoetherian_of_tower B' (inferInstance : IsNoetherian B' B)
  have hinjBF : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
  have hinjB'F' : Function.Injective (algebraMap B' F') := IsFractionRing.injective B' F'
  have hinjφ : Function.Injective φ := φ.toRingHom.injective
  have hinjι : Function.Injective (algebraMap B' B) := by
    intro x y hxy
    have h := congrArg (algebraMap B F) hxy
    rw [hι, hι] at h
    exact hinjB'F' (hinjφ h)
  haveI : FaithfulSMul B' B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjι
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hϖQ' : algebraMap A B' ϖ ∉ Q.under B' := by
    rw [Ideal.under_def, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]; exact hϖQ

  have hAQ : ∀ (C : Type) [CommRing C] [Algebra A C] (P : Ideal C) [P.IsPrime],
      algebraMap A C ϖ ∉ P → ∀ a : A, a ≠ 0 → algebraMap A C a ∉ P := by
    intro C _ _ P _ hP a ha haP
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hirr
    rw [map_mul, map_pow] at haP
    rcases (Ideal.IsPrime.mem_or_mem inferInstance haP) with hu | hpow
    · exact (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem _ hu ((Units.isUnit u).map _))
    · exact hP (Ideal.IsPrime.mem_of_pow_mem inferInstance n hpow)

  have hLfrac : ∀ (E : Type) [Field E] [Algebra L E] [Algebra A E] [IsScalarTower A L E]
      (C : Type) [CommRing C] [Algebra A C] [Algebra C E] [IsScalarTower A C E] (P : Ideal C) [P.IsPrime],
      algebraMap A C ϖ ∉ P →
      ∀ c : L, ∃ a b : C, b ∉ P ∧ algebraMap L E c * algebraMap C E b = algebraMap C E a := by
    intro E _ _ _ _ C _ _ _ _ P _ hP c
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) c
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    refine ⟨algebraMap A C x, algebraMap A C y, hAQ C P hP y hy0, ?_⟩
    have hyL : algebraMap A L y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr hy0
    rw [← IsScalarTower.algebraMap_apply A C E, ← IsScalarTower.algebraMap_apply A C E,
      IsScalarTower.algebraMap_apply A L E y, IsScalarTower.algebraMap_apply A L E x, map_div₀,
      div_mul_cancel₀ _ ((map_ne_zero_iff _ (algebraMap L E).injective).mpr hyL)]

  obtain ⟨w, hwmem, hwA, hwnu, hword0, hwordQ⟩ :=
    exists_place_of_height_eq_one L F B Q hQ1 (hLfrac F B Q hϖQ)
  have hordj : 0 ≤ w.ord (algebraMap B F jB) := hword0 jB

  obtain ⟨f, hf0, hf1⟩ : ∃ f : F', f ≠ 0 ∧ w.ord (φ f) = 1 := by
    letI := AlgebraicCurve.algebraAlong φ
    haveI := AlgebraicCurve.isIntegral_along φ hint
    obtain ⟨f, hf0, hf⟩ := w.exists_ord_eq_ramificationIndex (F := F')
    refine ⟨f, hf0, ?_⟩
    have : AlgebraicCurve.Place.ramificationIndex (F := F') w = AlgebraicCurve.Place.ramificationIndexAlong φ w := rfl
    rw [this, he w hordj] at hf
    exact_mod_cast hf

  have hQ'1 : (Q.under B').height = 1 := height_under_eq_one B' B Q hQ1
  obtain ⟨w', hw'mem, hw'A, hw'nu, hw'ord0, hw'ordQ⟩ :=
    exists_place_of_height_eq_one L F' B' (Q.under B') hQ'1 (hLfrac F' B' (Q.under B') hϖQ')

  let W : ValuationSubring F' := w.toValuationSubring.comap φ.toRingHom
  have hW : ∀ x : F', x ∈ W ↔ φ x ∈ w.toValuationSubring := fun _ => Iff.rfl
  have hw'W : w'.toValuationSubring ≤ W := by
    intro x hx
    rw [hW]
    obtain ⟨r, s, hs, hx⟩ := (hw'mem x).mp hx
    refine (hwmem _).mpr ⟨algebraMap _ _ r, algebraMap _ _ s, fun h => hs h, ?_⟩
    have := congrArg φ hx
    rw [map_mul] at this
    rw [hι, hι]
    exact this
  have hQ'0 : Q.under B' ≠ ⊥ := by
    intro h; rw [h, Ideal.height_bot] at hQ'1; exact zero_ne_one hQ'1
  have hWtop : W ≠ ⊤ := by
    obtain ⟨q, hqQ, hq0⟩ := (Q.under B').ne_bot_iff.mp hQ'0
    intro htop
    have hmemW : (algebraMap B' F' q)⁻¹ ∈ W := htop ▸ Subring.mem_top _
    rw [hW, map_inv₀, ← hι] at hmemW
    have hnu : algebraMap B F (algebraMap B' B q) ∈ w.toValuationSubring.nonunits := (hwnu _).mpr hqQ
    rw [ValuationSubring.mem_nonunits_iff_or] at hnu
    rcases hnu with h0 | hninv
    · exact hq0 (hinjι (hinjBF (by rw [h0, map_zero, map_zero])))
    · exact hninv hmemW
  have hWeq : w'.toValuationSubring = W := ValuationSubring.eq_of_le_of_ne_top _ hw'W hWtop

  have hordA' : ∀ s : B', s ∉ Q.under B' → w.ord (φ (algebraMap B' F' s)) = 0 := by
    intro s hs
    rw [← hι]
    have hs' : algebraMap B' B s ∉ Q := hs
    have hne : algebraMap B' B s ≠ 0 := fun h => hs' (h ▸ Q.zero_mem)
    have h0 := hword0 (algebraMap B' B s)
    have h1 := (hwordQ _ hne).not.mpr hs'
    omega

  obtain ⟨r, hrQ', hr1⟩ : ∃ r : B', r ∈ Q.under B' ∧ w.ord (algebraMap B F (algebraMap B' B r)) = 1 := by
    have hif0 : φ f ≠ 0 := fun h => hf0 (hinjφ (h.trans (map_zero φ).symm))
    have hfW : f ∈ W := (hW f).mpr (mem_of_ord_nonneg w hif0 (by rw [hf1]; norm_num))
    rw [← hWeq] at hfW
    obtain ⟨r, s, hs, hrs⟩ := (hw'mem f).mp hfW
    have hs0 : algebraMap B' F' s ≠ 0 := fun h =>
      hs ((show s = 0 from hinjB'F' (by rw [h, map_zero])) ▸ Ideal.zero_mem _)
    have := congrArg φ hrs
    rw [map_mul] at this
    have hs0K : φ (algebraMap B' F' s) ≠ 0 := fun h => hs0 (hinjφ (h.trans (map_zero φ).symm))
    have hord := congrArg w.ord this
    rw [w.ord_mul hif0 hs0K, hf1, hordA' s hs, add_zero] at hord
    refine ⟨r, ?_, by rw [hι]; exact hord.symm⟩
    have hr0 : algebraMap B' B r ≠ 0 := by
      intro h
      have : w.ord (φ (algebraMap B' F' r)) = 0 := by rw [← hι, h]; simp
      omega
    change algebraMap B' B r ∈ Q
    refine (hwordQ _ hr0).mp ?_
    rw [hι, ← hord]; norm_num

  have hr0K : algebraMap B F (algebraMap B' B r) ≠ 0 := by
    intro h; rw [h] at hr1; simp at hr1
  have key : Q.map (algebraMap B (Localization.AtPrime Q)) ≤ (Q.under B').map (algebraMap B' (Localization.AtPrime Q)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap]
    rcases eq_or_ne q 0 with rfl | hq0
    · rw [map_zero]; exact Ideal.zero_mem _
    have hq0K : algebraMap B F q ≠ 0 := (map_ne_zero_iff _ hinjBF).mpr hq0
    have hordq : 1 ≤ w.ord (algebraMap B F q) := (hwordQ q hq0).mpr hq
    have hx : algebraMap B F q * (algebraMap B F (algebraMap B' B r))⁻¹ ∈ w.toValuationSubring := by
      refine mem_of_ord_nonneg w (mul_ne_zero hq0K (inv_ne_zero hr0K)) ?_
      rw [w.ord_mul hq0K (inv_ne_zero hr0K), w.ord_inv, hr1]
      omega
    obtain ⟨b, t, ht, hbt⟩ := (hwmem _).mp hx
    have heq : q * t = algebraMap B' B r * b := by
      apply hinjBF
      rw [map_mul, map_mul, ← hbt]
      field_simp
    have htu : IsUnit (algebraMap B (Localization.AtPrime Q) t) :=
      IsLocalization.map_units _ (⟨t, ht⟩ : Q.primeCompl)
    have := congrArg (algebraMap B (Localization.AtPrime Q)) heq
    rw [map_mul, map_mul] at this
    have hq' : algebraMap B (Localization.AtPrime Q) q =
        algebraMap B (Localization.AtPrime Q) (algebraMap B' B r) *
          (algebraMap B (Localization.AtPrime Q) b * ↑(htu.unit⁻¹)) := by
      rw [← mul_assoc, ← this, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [hq', ← IsScalarTower.algebraMap_apply]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hrQ')

  haveI : CharZero A := (algebraMap A L).charZero
  refine isUnramifiedAt_of_map_le B' B Q (fun n hn => ?_) key
  have hnA : (n : A) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have := hAQ B' (Q.under B') hϖQ' (n : A) hnA
  rwa [map_natCast] at this

end L5hAux

open L5hAux in

theorem solution
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (F : Type) [Field F] [Algebra L F] [Algebra A F] [IsScalarTower A L F]
    (F' : Type) [Field F'] [Algebra L F'] [Algebra A F'] [IsScalarTower A L F']
    (φ : F' →ₐ[L] F)
    (B : Type) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Algebra B F] [IsScalarTower A B F]
    [IsFractionRing B F]
    (B' : Type) [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B'] [Algebra A B'] [Algebra B' F']
    [IsScalarTower A B' F'] [IsFractionRing B' F']
    [Algebra B' B] [IsScalarTower A B' B] [Module.Finite B' B]
    (hι : ∀ x : B', algebraMap B F (algebraMap B' B x) = φ (algebraMap B' F' x))
    (hint : φ.toRingHom.IsIntegral)
    (jB : B)
    (he : ∀ w : AlgebraicCurve.Place L F, 0 ≤ w.ord (algebraMap B F jB) →
      AlgebraicCurve.Place.ramificationIndexAlong φ w = 1)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (Q : Ideal B) [Q.IsPrime] (hQ1 : Q.height = 1)
    (hϖQ : algebraMap A B ϖ ∉ Q) :
    Algebra.IsUnramifiedAt B' Q :=
  isUnramifiedAt_of_height_eq_one_of_not_mem_of_ramificationIndexAlong_eq_one L A F F' φ B B' hι hint jB he ϖ hϖ Q hQ1 hϖQ

end S_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one
end P2MW
export P2MW.S_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one (solution)
