-- Prove2me | solution 1 for AlgebraicCurve.Place.ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/01d0c1d6-a6c2-5cc8-949b-a51c658c8550

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_isUnit_norm_aeval_derivative_minpoly
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem

set_option autoImplicit false

p2m_open "Polynomial AlgebraicCurve P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.restrictAlong Place.ramificationIndexAlong Place.ramificationIndex_le_ord Place.ramificationIndex_pos Place Place.ord_zero"
namespace KummerUnram
p2m_open "AlgebraicCurve"

section Transport
variable {K K' : Type*} [Field K] [Field K']

theorem mem_nonunits_comap_iff (A : ValuationSubring K') (φ : K →+* K') (x : K) :
    x ∈ (A.comap φ).nonunits ↔ φ x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, map_eq_zero_iff φ φ.injective,
    ← map_inv₀, ValuationSubring.mem_comap]

theorem inv_mem_of_not_mem_nonunits (A : ValuationSubring K) {x : K} (h : x ∉ A.nonunits) : x⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at h
  exact h.2

theorem ne_top_of_mem_nonunits (A : ValuationSubring K) {x : K} (hx : x ∈ A.nonunits) (hx0 : x ≠ 0) : A ≠ ⊤ := by
  intro h
  rw [ValuationSubring.mem_nonunits_iff_or] at hx
  rcases hx with hx | hx
  · exact hx0 hx
  · apply hx; rw [h]; trivial

theorem mem_nonunits_of_mem_of_not_isUnit (A : ValuationSubring K) {x : K} (hx : x ∈ A) (h : ¬ IsUnit (⟨x, hx⟩ : A)) :
    x ∈ A.nonunits :=
  ValuationSubring.coe_mem_nonunits_iff.mpr h

theorem nonunits_mul_mem (A : ValuationSubring K) {x y : K} (hx : x ∈ A.nonunits) (hy : y ∈ A) : x * y ∈ A.nonunits := by
  have hxA : x ∈ A := A.nonunits_le hx
  have h1 : (⟨x, hxA⟩ : A) ∈ IsLocalRing.maximalIdeal A := ValuationSubring.coe_mem_nonunits_iff.mp hx
  have h2 := Ideal.mul_mem_right (⟨y, hy⟩ : A) _ h1
  exact ValuationSubring.coe_mem_nonunits_iff.mpr h2

theorem not_mem_nonunits_of_inv_mem (A : ValuationSubring K) {x : K} (hx0 : x ≠ 0) (hxi : x⁻¹ ∈ A) : x ∉ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not]
  exact ⟨hx0, hxi⟩

theorem valuation_eq_one_of_mem_of_not_mem_nonunits (A : ValuationSubring K) {x : K} (hx : x ∈ A) (hxn : x ∉ A.nonunits) :
    A.valuation x = 1 :=
  le_antisymm ((A.valuation_le_one_iff x).mpr hx) (not_lt.mp (fun h => hxn (A.mem_nonunits_iff.mpr h)))

end Transport

end AlgebraicCurve.KummerUnram

open AlgebraicCurve.KummerUnram in

theorem solution
    {k F F' : Type*} [Field k] [IsAlgClosed k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (c : F') (hgen : Subfield.closure (Set.range φ ∪ {c}) = ⊤)
    (u : F) (hu : φ u = c ^ n)
    (P : AlgebraicCurve.Place k F')
    (hrat : (P.restrictAlong φ hφ).IsRational)
    (huP : u ∈ (P.restrictAlong φ hφ).toValuationSubring ∧ u⁻¹ ∈ (P.restrictAlong φ hφ).toValuationSubring) :
    P.ramificationIndexAlong φ = 1 := by
  classical

  letI alg : Algebra F F' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  haveI : Algebra.IsIntegral F F' := ⟨hφ⟩
  have hφa : ∀ x : F, algebraMap F F' x = φ x := fun _ => rfl
  show P.ramificationIndex F = 1
  set v : Place k F := P.restrict F with hvdef
  have hv : P.restrictAlong φ hφ = v := rfl
  rw [hv] at hrat huP
  set 𝒪 : ValuationSubring F := v.toValuationSubring with h𝒪def
  set A : ValuationSubring F' := P.toValuationSubring with hAdef
  have hvA : ∀ x : F, x ∈ 𝒪 ↔ algebraMap F F' x ∈ A := fun x => Iff.rfl
  have hvAn : ∀ x : F, x ∈ 𝒪.nonunits ↔ algebraMap F F' x ∈ A.nonunits := fun x =>
    mem_nonunits_comap_iff A (algebraMap F F') x
  obtain ⟨hu𝒪, hui𝒪⟩ := huP

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ1 : P.ord (ϖ : F') = 1 := P.ord_coe_irreducible hϖ
  have crit : ∀ f : F, P.ord (algebraMap F F' f) = 1 → P.ramificationIndex F = 1 := by
    intro f hf
    have hf0 : f ≠ 0 := by rintro rfl; rw [map_zero, Place.ord_zero] at hf; exact zero_ne_one hf
    have h1 := P.ramificationIndex_le_ord (F := F) hf0 (by rw [hf]; exact zero_lt_one)
    have h2 := P.ramificationIndex_pos (F := F)
    rw [hf] at h1
    omega

  have hadj : IntermediateField.adjoin F ({c} : Set F') = ⊤ := by
    apply IntermediateField.toSubfield_injective
    show Subfield.closure (Set.range (algebraMap F F') ∪ {c}) = (⊤ : IntermediateField F F').toSubfield
    rw [show Set.range (algebraMap F F') = Set.range φ from rfl, hgen]
    rfl

  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  by_cases hu0 : u = 0
  · subst hu0
    have hc0 : c = 0 := pow_eq_zero_iff hn0 |>.mp (by rw [← hu, map_zero])
    subst hc0

    have hsurj : Function.Surjective (algebraMap F F') := by
      intro y
      have hy : y ∈ (⊤ : IntermediateField F F') := IntermediateField.mem_top
      rw [← hadj, IntermediateField.adjoin_zero] at hy
      exact IntermediateField.mem_bot.mp hy
    obtain ⟨f, hf⟩ := hsurj (ϖ : F')
    exact crit f (by rw [hf]; exact hϖ1)

  have hkF : Function.Injective (algebraMap k F) := (algebraMap k F).injective
  have hnF : (n : F) ≠ 0 := by
    intro h; apply hn; apply hkF; rw [map_natCast, h, map_zero]
  have hc0 : c ≠ 0 := by
    intro h; apply hu0
    apply (algebraMap F F').injective
    rw [hφa, hu, h, zero_pow hn0, map_zero]
  have hcF : IsIntegral F c := ⟨X ^ n - C u, monic_X_pow_sub_C u hn0, by simp [hφa, hu]⟩
  haveI : FiniteDimensional F F' := by
    haveI := IntermediateField.adjoin.finiteDimensional hcF
    rw [hadj] at this
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  have hsepc : IsSeparable F c := by
    have hdvd : minpoly F c ∣ X ^ n - C u := minpoly.dvd F c (by simp [hφa, hu])
    exact (separable_X_pow_sub_C u hnF hu0).of_dvd hdvd
  haveI : Algebra.IsSeparable F F' := by
    haveI := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F F').mpr hsepc
    rw [hadj] at this
    exact AlgEquiv.Algebra.isSeparable IntermediateField.topEquiv

  haveI : IsPrincipalIdealRing 𝒪 := v.isPrincipalIdealRing'
  letI alg𝒪 : Algebra 𝒪 F' := ((algebraMap F F').comp 𝒪.subtype).toAlgebra
  haveI : IsScalarTower 𝒪 F F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hc𝒪 : IsIntegral 𝒪 c :=
    ⟨X ^ n - C ⟨u, hu𝒪⟩, monic_X_pow_sub_C _ hn0, by simp [eval₂_sub, eval₂_X_pow, hφa, hu, IsScalarTower.algebraMap_apply 𝒪 F F']⟩
  set S := integralClosure 𝒪 F' with hSdef
  have hcS : c ∈ S := hc𝒪
  have hadjS : Algebra.adjoin 𝒪 {c} ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hcS)
  have hSint : ∀ s ∈ S, IsIntegral 𝒪 s := fun s hs => hs

  have hnorm : ∀ x : F', IsIntegral 𝒪 x → ∃ y : 𝒪, algebraMap 𝒪 F y = Algebra.norm F x := fun x hx =>
    IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm F hx)

  haveI : Module.IsTorsionFree 𝒪 F' :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr ((algebraMap F F').injective.comp Subtype.val_injective)
  have hci : IsIntegral 𝒪 c⁻¹ := by
    have h1 : (algebraMap 𝒪 F' ⟨u⁻¹, hui𝒪⟩ : F') = (c ^ n)⁻¹ := by
      rw [IsScalarTower.algebraMap_apply 𝒪 F F']
      show algebraMap F F' u⁻¹ = _
      rw [map_inv₀, hφa, hu]
    have h2 : c ^ n = c ^ (n - 1) * c := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
    have : c⁻¹ = c ^ (n - 1) * algebraMap 𝒪 F' ⟨u⁻¹, hui𝒪⟩ := by
      rw [h1, h2]
      field_simp
    rw [this]
    exact (hc𝒪.pow _).mul isIntegral_algebraMap
  obtain ⟨yc, hyc⟩ := hnorm c hc𝒪
  obtain ⟨yci, hyci⟩ := hnorm c⁻¹ hci
  have hycu : IsUnit yc := by
    refine IsUnit.of_mul_eq_one yci ((IsFractionRing.injective 𝒪 F) ?_)
    rw [map_mul, hyc, hyci, map_one, ← map_mul, mul_inv_cancel₀ hc0, map_one]

  have hnmem : ((n : ℕ) : F) ∈ 𝒪 := by rw [← map_natCast (algebraMap k F)]; exact v.algebraMap_mem' _
  have hnu : IsUnit (⟨(n : F), hnmem⟩ : 𝒪) := by
    refine IsUnit.of_mul_eq_one ⟨algebraMap k F ((n : k)⁻¹), v.algebraMap_mem' _⟩ (Subtype.ext ?_)
    show (n : F) * algebraMap k F ((n : k)⁻¹) = 1
    rw [map_inv₀, map_natCast, mul_inv_cancel₀ hnF]

  set g𝒪 := minpoly 𝒪 c with hg𝒪
  have hg : minpoly F c = g𝒪.map (algebraMap 𝒪 F) := minpoly.isIntegrallyClosed_eq_field_fractions' F hc𝒪
  set f𝒪 : 𝒪[X] := X ^ n - C ⟨u, hu𝒪⟩ with hf𝒪
  have hf : f𝒪.map (algebraMap 𝒪 F) = X ^ n - C u := by simp [hf𝒪]
  have hgdvd : g𝒪 ∣ f𝒪 := minpoly.isIntegrallyClosed_dvd hc𝒪 (by simp [hf𝒪, hφa, hu, IsScalarTower.algebraMap_apply 𝒪 F F'])
  obtain ⟨h𝒪, hfgh⟩ := hgdvd

  have haeval𝒪 : ∀ q : 𝒪[X], aeval c q = aeval c (q.map (algebraMap 𝒪 F)) := fun q => (aeval_map_algebraMap F c q).symm
  have hgc : aeval c g𝒪 = 0 := minpoly.aeval 𝒪 c
  have hder : aeval c (derivative (minpoly F c)) * aeval c h𝒪 = algebraMap F F' n * c ^ (n - 1) := by
    have h1 : derivative f𝒪 = derivative g𝒪 * h𝒪 + g𝒪 * derivative h𝒪 := by rw [hfgh, derivative_mul]
    have h2 : aeval c (derivative f𝒪) = aeval c (derivative g𝒪) * aeval c h𝒪 := by
      rw [h1, map_add, map_mul, map_mul, hgc, zero_mul, add_zero]
    have h3 : aeval c (derivative f𝒪) = algebraMap F F' n * c ^ (n - 1) := by
      simp [hf𝒪, derivative_X_pow, map_natCast]
    rw [hg, derivative_map, ← haeval𝒪, ← h2, h3]

  have hhint : IsIntegral 𝒪 (aeval c h𝒪) := hSint _ (hadjS (aeval_mem_adjoin_singleton 𝒪 c))
  have hgint : IsIntegral 𝒪 (aeval c (derivative (minpoly F c))) := by
    rw [hg, derivative_map, ← haeval𝒪]; exact hSint _ (hadjS (aeval_mem_adjoin_singleton 𝒪 c))
  obtain ⟨y₁, hy₁⟩ := hnorm _ hgint
  obtain ⟨y₂, hy₂⟩ := hnorm _ hhint
  have hprod : y₁ * y₂ = ⟨(n : F), hnmem⟩ ^ Module.finrank F F' * yc ^ (n - 1) := by
    apply IsFractionRing.injective 𝒪 F
    rw [map_mul, hy₁, hy₂, ← map_mul, hder, map_mul, map_pow, map_mul, map_pow, map_pow, hyc, Algebra.norm_algebraMap]
    rfl
  have hdisc : ∃ w : 𝒪ˣ, algebraMap 𝒪 F w = Algebra.norm F (aeval c (derivative (minpoly F c))) := by
    have hu12 : IsUnit (y₁ * y₂) := by rw [hprod]; exact (hnu.pow _).mul (hycu.pow _)
    obtain ⟨w, hw⟩ := isUnit_of_mul_isUnit_left hu12
    exact ⟨w, by rw [hw, hy₁]⟩

  have hSadj : ∀ s ∈ S, s ∈ Algebra.adjoin 𝒪 ({c} : Set F') := fun s hs =>
    ValuationSubring.mem_adjoin_singleton_of_isIntegral_of_isUnit_norm_aeval_derivative_minpoly 𝒪 c hc𝒪 hadj hdisc s hs
  have hSpoly : ∀ s ∈ S, ∃ q : 𝒪[X], aeval c q = s := by
    intro s hs
    have h := hSadj s hs
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h
    exact h

  haveI : IsDedekindDomain S := integralClosure.isDedekindDomain 𝒪 F F'
  haveI : IsFractionRing S F' := IsIntegralClosure.isFractionRing_of_finite_extension 𝒪 F F' S
  have hSA : ∀ s : F', s ∈ S → s ∈ A := by
    intro s hs

    have h𝒪A : ∀ o : 𝒪, algebraMap F F' (o : F) ∈ A := fun o => (hvA _).mp o.2
    let ψ : 𝒪 →+* A := ((algebraMap F F').comp 𝒪.subtype).codRestrict A.toSubring (fun o => h𝒪A o)
    obtain ⟨p, hp, hps⟩ := hSint s hs
    have hint : IsIntegral A s := by
      refine ⟨p.map ψ, hp.map ψ, ?_⟩
      rw [eval₂_map]
      exact hps
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [← hy]; exact y.2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hπm : (π : F) ∈ 𝒪.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    exact ⟨π.2, by simpa using hπ.not_isUnit⟩
  have hπA : algebraMap F F' (π : F) ∈ A.nonunits := (hvAn _).mp hπm
  have hπmemA : algebraMap F F' (π : F) ∈ A := A.nonunits_le hπA
  have hA_ne_top : A ≠ ⊤ :=
    ne_top_of_mem_nonunits A hπA (by rw [map_ne_zero_iff _ (algebraMap F F').injective]; exact hπ0)
  let incl : S →+* A := (algebraMap S F').codRestrict A.toSubring (fun s => hSA s s.2)
  let 𝔓 : Ideal S := (IsLocalRing.maximalIdeal A).comap incl
  have h𝔓mem : ∀ s : S, s ∈ 𝔓 ↔ (s : F') ∈ A.nonunits := by
    intro s
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]; rfl
  haveI h𝔓prime : 𝔓.IsPrime := Ideal.comap_isPrime _ _
  have hπS : (algebraMap F F' (π : F)) ∈ S := by
    show IsIntegral 𝒪 _
    have : algebraMap F F' (π : F) = algebraMap 𝒪 F' π := rfl
    rw [this]; exact isIntegral_algebraMap
  have h𝔓ne : 𝔓 ≠ ⊥ := by
    intro h
    have hmem : (⟨algebraMap F F' (π : F), hπS⟩ : S) ∈ 𝔓 := (h𝔓mem _).mpr hπA
    rw [h, Ideal.mem_bot, Subtype.ext_iff] at hmem
    exact (map_ne_zero_iff _ (algebraMap F F').injective).mpr hπ0 hmem
  let w : IsDedekindDomain.HeightOneSpectrum S := ⟨𝔓, h𝔓prime, h𝔓ne⟩
  have hloc : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F' w = A := by
    refine ValuationSubring.eq_of_le_of_ne_top _ ?_ hA_ne_top
    rintro y ⟨a, s, hs, rfl⟩
    have ha : ((a : S) : F') ∈ A := hSA _ a.2
    have hsn : ((s : S) : F') ∉ A.nonunits := fun hn' => hs ((h𝔓mem s).mpr hn')
    exact A.mul_mem _ _ ha (inv_mem_of_not_mem_nonunits A hsn)

  have hfrac : ∀ x : F', x ∈ A.nonunits → ∃ a s : S, a ∈ 𝔓 ∧ (s : F') ∉ A.nonunits ∧ x * (s : F') = a := by
    intro x hx
    have hxA : x ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F' w := by rw [hloc]; exact A.nonunits_le hx
    obtain ⟨a, s, hs, rfl⟩ := hxA
    have hsn : ((s : S) : F') ∉ A.nonunits := fun hn' => hs ((h𝔓mem s).mpr hn')
    have hs0 : ((s : S) : F') ≠ 0 := fun h0 => hsn (by rw [h0]; exact A.nonunits.zero_mem)
    have hxs : algebraMap S F' a * (algebraMap S F' s)⁻¹ * (s : F') = (a : F') := by
      show (a : F') * ((s : F'))⁻¹ * (s : F') = (a : F')
      rw [inv_mul_cancel_right₀ hs0]
    refine ⟨a, s, ?_, hsn, hxs⟩
    rw [h𝔓mem, ← hxs]
    exact nonunits_mul_mem A hx (hSA _ s.2)

  obtain ⟨u₀, hu₀⟩ := hrat (IsLocalRing.residue 𝒪 ⟨u, hu𝒪⟩)
  have huunit : IsUnit (⟨u, hu𝒪⟩ : 𝒪) := IsUnit.of_mul_eq_one ⟨u⁻¹, hui𝒪⟩ (Subtype.ext (mul_inv_cancel₀ hu0))
  have hdiff : (⟨u, hu𝒪⟩ : 𝒪) - algebraMap k 𝒪 u₀ ∈ IsLocalRing.maximalIdeal 𝒪 := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← IsLocalRing.ResidueField.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply k 𝒪, hu₀, IsLocalRing.ResidueField.algebraMap_eq, sub_self]
  have hu₀0 : u₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero] at hdiff
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hdiff) huunit
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : 𝒪, t₀ * π = ⟨u, hu𝒪⟩ - algebraMap k 𝒪 u₀ := by
    rw [← Ideal.mem_span_singleton', ← hπ.maximalIdeal_eq]; exact hdiff
  set πA : F' := algebraMap F F' (π : F) with hπAdef
  have hcong : c ^ n - algebraMap k F' u₀ = πA * algebraMap F F' (t₀ : F) := by
    have h : ((t₀ * π : 𝒪) : F) = ((⟨u, hu𝒪⟩ - algebraMap k 𝒪 u₀ : 𝒪) : F) := congrArg (fun o : 𝒪 => (o : F)) ht₀
    rw [MulMemClass.coe_mul, AddSubgroupClass.coe_sub] at h
    have h' : (t₀ : F) * (π : F) = u - algebraMap k F u₀ := h
    calc c ^ n - algebraMap k F' u₀ = algebraMap F F' (u - algebraMap k F u₀) := by
            rw [map_sub, hφa u, hu, ← IsScalarTower.algebraMap_apply k F F']
      _ = algebraMap F F' ((t₀ : F) * (π : F)) := by rw [h']
      _ = πA * algebraMap F F' (t₀ : F) := by rw [map_mul, mul_comm]

  set q₀ : k[X] := X ^ n - C u₀ with hq₀
  have hq₀m : q₀.Monic := monic_X_pow_sub_C u₀ hn0
  have hsplit : q₀.Splits := IsAlgClosed.splits q₀
  set R := q₀.roots with hR
  have hRprod : (R.map fun r => X - C r).prod = q₀ := (hsplit.eq_prod_roots_of_monic hq₀m).symm
  have hRnodup : R.Nodup := nodup_roots (separable_X_pow_sub_C u₀ hn hu₀0)

  set xr : k → F' := fun r => c - algebraMap k F' r with hxr
  have hcA : c ∈ A := hSA c hcS
  have hconstA : ∀ y : k, algebraMap k F' y ∈ A := fun y => P.algebraMap_mem' y
  have hxrA : ∀ r, xr r ∈ A := fun r => A.sub_mem hcA (hconstA r)
  have hconst_unit : ∀ y : k, y ≠ 0 → algebraMap k F' y ∉ A.nonunits := fun y hy =>
    not_mem_nonunits_of_inv_mem A ((map_ne_zero_iff _ (algebraMap k F').injective).mpr hy)
      (by rw [← map_inv₀]; exact hconstA _)
  have hprodR : (R.map xr).prod = πA * algebraMap F F' (t₀ : F) := by
    rw [← hcong]
    have h := congrArg (aeval c) hRprod
    rw [map_multiset_prod, Multiset.map_map] at h
    have h' : (aeval c) q₀ = c ^ n - algebraMap k F' u₀ := by simp [hq₀]
    rw [← h', ← h]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    simp [hxr]

  have hprod_nonunit : (R.map xr).prod ∈ A.nonunits := by
    rw [hprodR]; exact nonunits_mul_mem A hπA ((hvA _).mp t₀.2)
  obtain ⟨rᵢ, hrᵢR, hrᵢ⟩ : ∃ rᵢ ∈ R, xr rᵢ ∈ A.nonunits := by
    by_contra hcon
    push Not at hcon
    have h1 : ∀ y ∈ R.map (fun r => A.valuation (xr r)), y = 1 := by
      intro y hy
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
      exact valuation_eq_one_of_mem_of_not_mem_nonunits A (hxrA r) (hcon r hr)
    have h2 : A.valuation (R.map xr).prod = 1 := by
      rw [map_multiset_prod, Multiset.map_map]
      exact Multiset.prod_eq_one h1
    exact (lt_irrefl (1 : _)) (h2 ▸ A.mem_nonunits_iff.mp hprod_nonunit)

  have hothers : ∀ r ∈ R.erase rᵢ, xr r ∉ A.nonunits := by
    intro r hr hrn
    have hne : r ≠ rᵢ := by
      rintro rfl
      exact (Multiset.nodup_iff_count_le_one.mp hRnodup r |> fun h => by
        have h2 : 2 ≤ R.count r := by
          have := Multiset.count_erase_self r R
          have hpos : 0 < (R.erase r).count r := Multiset.count_pos.mpr hr
          omega
        omega)
    have hdiffn : xr r - xr rᵢ ∈ A.nonunits := A.nonunits.sub_mem hrn hrᵢ
    have heq : xr r - xr rᵢ = algebraMap k F' (rᵢ - r) := by simp only [hxr, map_sub]; ring
    rw [heq] at hdiffn
    exact hconst_unit _ (sub_ne_zero.mpr hne.symm) hdiffn

  have hxi : ∃ b ∈ A, xr rᵢ = πA * b := by
    have hsplitprod := Multiset.prod_map_erase (f := xr) hrᵢR

    set Q := ((R.erase rᵢ).map xr).prod with hQ
    have hQA : Q ∈ A := A.toSubring.multiset_prod_mem _ (by
      intro y hy; obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hy; exact hxrA r)
    have hQ1 : A.valuation Q = 1 := by
      rw [hQ, map_multiset_prod, Multiset.map_map]
      apply Multiset.prod_eq_one
      intro y hy
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
      exact valuation_eq_one_of_mem_of_not_mem_nonunits A (hxrA r) (hothers r hr)
    have hQ0 : Q ≠ 0 := fun h => by rw [h, map_zero] at hQ1; exact zero_ne_one hQ1
    have hQi : Q⁻¹ ∈ A := by
      apply (A.valuation_le_one_iff _).mp
      rw [map_inv₀, hQ1, inv_one]
    refine ⟨algebraMap F F' (t₀ : F) * Q⁻¹, mul_mem ((hvA _).mp t₀.2) hQi, ?_⟩
    rw [← mul_assoc, ← hprodR, ← hsplitprod, mul_inv_cancel_right₀ hQ0]
  obtain ⟨bᵢ, hbᵢA, hbᵢ⟩ := hxi

  have hρmem : algebraMap k F rᵢ ∈ 𝒪 := v.algebraMap_mem' rᵢ
  set ρ : 𝒪 := ⟨algebraMap k F rᵢ, hρmem⟩ with hρ
  have hρF' : algebraMap 𝒪 F' ρ = algebraMap k F' rᵢ := by
    show algebraMap F F' (algebraMap k F rᵢ) = _
    rw [← IsScalarTower.algebraMap_apply k F F']
  have h𝔓π : ∀ a : F', a ∈ S → a ∈ A.nonunits → ∃ b ∈ A, a = πA * b := by
    intro a haS han
    obtain ⟨q, rfl⟩ := hSpoly a haS

    have hdiv := modByMonic_add_div q (X - C ρ)
    rw [modByMonic_X_sub_C_eq_C_eval] at hdiv
    set q₁ := q /ₘ (X - C ρ) with hq₁
    have hq : aeval c q = algebraMap 𝒪 F' (q.eval ρ) + xr rᵢ * aeval c q₁ := by
      conv_lhs => rw [← hdiv]
      rw [map_add, map_mul, aeval_C, map_sub, aeval_X, aeval_C, hρF']

    have hq₁A : aeval c q₁ ∈ A := hSA _ (hadjS (aeval_mem_adjoin_singleton 𝒪 c))
    have h2 : xr rᵢ * aeval c q₁ = πA * (bᵢ * aeval c q₁) := by rw [hbᵢ, mul_assoc]
    have h2n : xr rᵢ * aeval c q₁ ∈ A.nonunits := nonunits_mul_mem A hrᵢ hq₁A

    have h1n : algebraMap 𝒪 F' (q.eval ρ) ∈ A.nonunits := by
      have : algebraMap 𝒪 F' (q.eval ρ) = aeval c q - xr rᵢ * aeval c q₁ := by rw [hq, add_sub_cancel_right]
      rw [this]
      exact A.nonunits.sub_mem han h2n
    have h1n' : ((q.eval ρ : 𝒪) : F) ∈ 𝒪.nonunits := (hvAn _).mpr h1n
    have h1m : q.eval ρ ∈ IsLocalRing.maximalIdeal 𝒪 := ValuationSubring.coe_mem_nonunits_iff.mp h1n'
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at h1m
    obtain ⟨t₁, ht₁⟩ := h1m
    have h1 : algebraMap 𝒪 F' (q.eval ρ) = πA * algebraMap F F' (t₁ : F) := by
      rw [← ht₁, map_mul, mul_comm]; rfl
    refine ⟨algebraMap F F' (t₁ : F) + bᵢ * aeval c q₁, add_mem ((hvA _).mp t₁.2) (mul_mem hbᵢA hq₁A), ?_⟩
    rw [hq, h1, h2, mul_add]

  have hmax : ∀ x : F', x ∈ A.nonunits → ∃ b ∈ A, x = πA * b := by
    intro x hx
    obtain ⟨a, s, ha𝔓, hsn, hxs⟩ := hfrac x hx
    obtain ⟨b, hbA, hb⟩ := h𝔓π (a : F') a.2 ((h𝔓mem a).mp ha𝔓)
    have hs0 : ((s : S) : F') ≠ 0 := fun h0 => hsn (by rw [h0]; exact A.nonunits.zero_mem)
    have hsi : ((s : S) : F')⁻¹ ∈ A := inv_mem_of_not_mem_nonunits A hsn
    refine ⟨b * ((s : S) : F')⁻¹, mul_mem hbA hsi, ?_⟩
    rw [← mul_assoc, ← hb, ← hxs, mul_inv_cancel_right₀ hs0]
  have hspan : IsLocalRing.maximalIdeal A = Ideal.span {(⟨πA, hπmemA⟩ : A)} := by
    apply le_antisymm
    · intro x hx
      have hxn : (x : F') ∈ A.nonunits := ValuationSubring.coe_mem_nonunits_iff.mpr hx
      obtain ⟨b, hbA, hb⟩ := hmax _ hxn
      rw [Ideal.mem_span_singleton']
      refine ⟨⟨b, hbA⟩, Subtype.ext ?_⟩
      show b * πA = (x : F')
      rw [mul_comm]; exact hb.symm
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact ValuationSubring.coe_mem_nonunits_iff.mp hπA
  have hirr : Irreducible (⟨πA, hπmemA⟩ : A) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hspan
  have hord : P.ord ((⟨πA, hπmemA⟩ : A) : F') = 1 := P.ord_coe_irreducible hirr
  have hcoe : ((⟨πA, hπmemA⟩ : A) : F') = algebraMap F F' (π : F) := by
    show πA = _
    exact hπAdef
  rw [hcoe] at hord
  exact crit (π : F) hord

end S_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem
end P2MW
export P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem (solution)
