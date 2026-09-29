-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_valuationSubring_algHom_apply_eq_forall_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/03c89347-e989-5413-a32d-13a895b50ec7

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_valuationSubring_algHom_apply_eq_forall_mem_iff
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.restrict_toValuationSubring Place Place.ext SemilinearAut SemilinearAut.ofAlgAut Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable Place.exists_algEquiv_smul_eq_of_restrict_eq"
p2m_open "AlgebraicCurve"
namespace PlaceRealisation

open IsLocalRing Polynomial
open scoped IntermediateField Pointwise

section Chevalley

variable {Ω : Type*} [Field Ω] {Ω' : Type*} [Field Ω'] [Algebra Ω Ω']

theorem exists_valuationSubring_over (A : ValuationSubring Ω) :
    ∃ O : ValuationSubring Ω', ∀ a : Ω, algebraMap Ω Ω' a ∈ O ↔ a ∈ A := by
  obtain ⟨O, hO, hloc⟩ :=
    IsLocalRing.exists_factor_valuationRing ((algebraMap Ω Ω').comp A.subtype)
  refine ⟨O, fun a => ⟨fun ha => ?_, fun ha => hO ⟨a, ha⟩⟩⟩
  by_contra hna

  have ha0 : a ≠ 0 := fun h => hna (h ▸ A.zero_mem)
  have hinv : a⁻¹ ∈ A := (A.mem_or_inv_mem a).resolve_left hna
  have hunitO : IsUnit (((algebraMap Ω Ω').comp A.subtype).codRestrict O.toSubring hO ⟨a⁻¹, hinv⟩) := by
    refine isUnit_iff_exists_inv.2 ⟨⟨algebraMap Ω Ω' a, ha⟩, Subtype.ext ?_⟩
    change algebraMap Ω Ω' (a⁻¹) * algebraMap Ω Ω' a = 1
    rw [← map_mul, inv_mul_cancel₀ ha0, map_one]
  have hunitA : IsUnit (⟨a⁻¹, hinv⟩ : A) := (isUnit_map_iff _ _).1 hunitO
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 hunitA
  have hb' : (b : Ω) = a := by
    have h1 : a⁻¹ * (b : Ω) = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    have h2 : (b : Ω) = (a⁻¹)⁻¹ := (eq_inv_of_mul_eq_one_right h1)
    rw [h2, inv_inv]
  exact hna (hb' ▸ b.2)

theorem mem_nonunits_of_over {A : ValuationSubring Ω} {O : ValuationSubring Ω'}
    (hO : ∀ a : Ω, algebraMap Ω Ω' a ∈ O ↔ a ∈ A) {a : Ω} (ha : a ∈ A.nonunits) :
    algebraMap Ω Ω' a ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at ha ⊢
  rcases ha with ha | ha
  · left; rw [ha, map_zero]
  · right; rw [← map_inv₀, hO]; exact ha

end Chevalley

section Nonunits

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem vs_ne_zero_of_notMem_nonunits {a : L} (ha : a ∉ A.nonunits) : a ≠ 0 := fun h =>
  ha (h ▸ A.nonunits.zero_mem)

theorem vs_inv_mem_of_notMem_nonunits {a : L} (ha : a ∉ A.nonunits) : a⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff_or] at ha
  push Not at ha
  exact ha.2

theorem vs_add_notMem_nonunits {a b : L} (ha : a ∉ A.nonunits) (hb : b ∈ A.nonunits) :
    a + b ∉ A.nonunits := fun h => ha (by simpa using A.nonunits.sub_mem h hb)

variable {A} in
theorem vs_mul_mem_nonunits {a x : L} (ha : a ∈ A) (hx : x ∈ A.nonunits) :
    a * x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  calc A.valuation (a * x) = A.valuation a * A.valuation x := map_mul _ _ _
    _ ≤ 1 * A.valuation x := mul_le_mul_left ((A.valuation_le_one_iff a).mpr ha) _
    _ = A.valuation x := one_mul _
    _ < 1 := hx

variable {A} in
theorem vs_one_notMem_nonunits : (1 : L) ∉ A.nonunits := by
  simp [ValuationSubring.mem_nonunits_iff]

end Nonunits

section RationalPlace

variable {L : Type*} [Field L] {M : Type*} [Field M] [Algebra L M]

theorem mem_iff_mem_of_sub_mem_nonunits (t : M) (ht : Transcendental L t) (j₀ : L)
    (V₁ V₂ : ValuationSubring M)
    (hL₁ : ∀ c : L, algebraMap L M c ∈ V₁) (hL₂ : ∀ c : L, algebraMap L M c ∈ V₂)
    (h₁ : t - algebraMap L M j₀ ∈ V₁.nonunits) (h₂ : t - algebraMap L M j₀ ∈ V₂.nonunits)
    (f : M) (hf : f ∈ L⟮t⟯) : f ∈ V₁ ↔ f ∈ V₂ := by
  set π : M := t - algebraMap L M j₀ with hπ
  have hπ0 : π ≠ 0 := fun h => by
    have : t = algebraMap L M j₀ := sub_eq_zero.1 h
    exact ht (this ▸ isAlgebraic_algebraMap j₀)

  have haeval : ∀ (V : ValuationSubring M), (∀ c : L, algebraMap L M c ∈ V) →
      π ∈ V.nonunits → ∀ p : L[X], aeval t p ∈ V := fun V hL h p => by
    have htV : t ∈ V := by
      have := add_mem (V.nonunits_subset h) (hL j₀)
      simpa [hπ] using this
    induction p using Polynomial.induction_on with
    | C a => simpa using hL a
    | add p q hp hq => simpa using add_mem hp hq
    | monomial n a _ =>
      rw [map_mul, map_pow, aeval_C, aeval_X]
      exact mul_mem (hL a) (pow_mem htV _)

  have hunit : ∀ (V : ValuationSubring M), (∀ c : L, algebraMap L M c ∈ V) →
      π ∈ V.nonunits → ∀ p : L[X], p.eval j₀ ≠ 0 → aeval t p ∉ V.nonunits := by
    intro V hL h p hp
    obtain ⟨q, hq⟩ : (X - C j₀) ∣ p - C (p.eval j₀) := by
      rw [dvd_iff_isRoot]; simp
    have hdec : aeval t p = algebraMap L M (p.eval j₀) + aeval t q * π := by
      have e := congrArg (aeval t) hq
      rw [map_sub, aeval_C, map_mul, map_sub, aeval_X, aeval_C] at e
      rw [hπ]; linear_combination e
    rw [hdec]
    refine vs_add_notMem_nonunits V ?_
      (vs_mul_mem_nonunits (haeval V hL h q) h)
    intro hc
    have hinv : (algebraMap L M (p.eval j₀))⁻¹ ∈ V := by
      rw [← map_inv₀]; exact hL _
    have hne : algebraMap L M (p.eval j₀) ≠ 0 := (_root_.map_ne_zero _).2 hp
    have h1 : (1 : M) ∈ V.nonunits := by
      have := vs_mul_mem_nonunits hinv hc
      rwa [inv_mul_cancel₀ hne] at this
    exact vs_one_notMem_nonunits h1

  rw [IntermediateField.mem_adjoin_simple_iff] at hf
  obtain ⟨r, s, rfl⟩ := hf
  by_cases hs : aeval t s = 0
  · rw [hs, div_zero]; exact ⟨fun _ => V₂.zero_mem, fun _ => V₁.zero_mem⟩
  by_cases hr : r = 0
  · rw [hr, map_zero, zero_div]; exact ⟨fun _ => V₂.zero_mem, fun _ => V₁.zero_mem⟩
  have hs0 : s ≠ 0 := fun h => hs (by rw [h, map_zero])

  obtain ⟨r₀, hr₀, hrdvd⟩ := r.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hr j₀
  obtain ⟨s₀, hs₀, hsdvd⟩ := s.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hs0 j₀
  have hr₀ev : r₀.eval j₀ ≠ 0 := fun h => hrdvd (dvd_iff_isRoot.2 h)
  have hs₀ev : s₀.eval j₀ ≠ 0 := fun h => hsdvd (dvd_iff_isRoot.2 h)
  set a := r.rootMultiplicity j₀ with ha
  set b := s.rootMultiplicity j₀ with hb
  set R₀ : M := aeval t r₀ with hR₀
  set S₀ : M := aeval t s₀ with hS₀
  have hR : aeval t r = π ^ a * R₀ := by
    conv_lhs => rw [hr₀]
    rw [map_mul, map_pow, map_sub, aeval_X, aeval_C]
  have hS : aeval t s = π ^ b * S₀ := by
    conv_lhs => rw [hs₀]
    rw [map_mul, map_pow, map_sub, aeval_X, aeval_C]

  have key : ∀ (V : ValuationSubring M), (∀ c : L, algebraMap L M c ∈ V) → π ∈ V.nonunits →
      (aeval t r / aeval t s ∈ V ↔ b ≤ a) := by
    intro V hL h
    have hR₀u : R₀ ∉ V.nonunits := hunit V hL h r₀ hr₀ev
    have hS₀u : S₀ ∉ V.nonunits := hunit V hL h s₀ hs₀ev
    have hR₀0 : R₀ ≠ 0 := vs_ne_zero_of_notMem_nonunits V hR₀u
    have hS₀0 : S₀ ≠ 0 := vs_ne_zero_of_notMem_nonunits V hS₀u
    have hR₀m : R₀ ∈ V := haeval V hL h r₀
    have hS₀m : S₀ ∈ V := haeval V hL h s₀
    have hπm : π ∈ V := V.nonunits_subset h
    constructor
    · intro hf
      by_contra hlt
      push Not at hlt

      obtain ⟨k, hk⟩ : ∃ k, b = a + (k + 1) := ⟨b - a - 1, by omega⟩
      have hnu : π ^ (k + 1) ∈ V.nonunits := by
        rw [pow_succ]; exact vs_mul_mem_nonunits (pow_mem hπm k) h
      have hprod : (aeval t r / aeval t s * (S₀ * R₀⁻¹)) * π ^ (k + 1) = 1 := by
        rw [hR, hS, hk, pow_add]
        field_simp
      have hmem : aeval t r / aeval t s * (S₀ * R₀⁻¹) ∈ V :=
        mul_mem hf (mul_mem hS₀m (vs_inv_mem_of_notMem_nonunits V hR₀u))
      have h1 : (1 : M) ∈ V.nonunits := by
        rw [← hprod]; exact vs_mul_mem_nonunits hmem hnu
      exact vs_one_notMem_nonunits h1
    · intro hle
      have heq : aeval t r / aeval t s = π ^ (a - b) * (R₀ * S₀⁻¹) := by
        rw [hR, hS, ← pow_sub_mul_pow π hle]
        field_simp
      rw [heq]
      exact mul_mem (pow_mem hπm _)
        (mul_mem hR₀m (vs_inv_mem_of_notMem_nonunits V hS₀u))
  exact (key V₁ hL₁ h₁).trans (key V₂ hL₂ h₂).symm

end RationalPlace

section Main

variable {K : Type*} [Field K] {M : Type*} [Field M] [Algebra K M]

theorem exists_algHom_adjoin_simple (t : M) (ht : Transcendental K t)
    {Ω' : Type*} [Field Ω'] [Algebra K Ω'] (j : Ω') (hj : Transcendental K j) :
    ∃ f₀ : K⟮t⟯ →ₐ[K] Ω', f₀ (IntermediateField.AdjoinSimple.gen K t) = j := by
  let e₁ := (RatFunc.algEquivOfTranscendental t ht).symm
  let e₂ := RatFunc.algEquivOfTranscendental j hj
  refine ⟨(IntermediateField.val _).comp (e₂.toAlgHom.comp e₁.toAlgHom), ?_⟩
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.coe_algHom]
  simp only [e₁, e₂, RatFunc.algEquivOfTranscendental_symm_gen]
  change ((RatFunc.algEquivOfTranscendental j hj (RatFunc.X : RatFunc K) : K⟮j⟯) : Ω') = j
  exact RatFunc.algEquivOfTranscendental_X j hj

theorem mem_nonunits_of_ord_pos {F : Type*} [Field F] [Algebra K F] (v : Place K F) {f : F}
    (h : 0 < v.ord f) : f ∈ v.toValuationSubring.nonunits := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact (v.toValuationSubring.nonunits).zero_mem
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  have hmem : f ∈ v.toValuationSubring := by
    rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h.le).symm,
      zpow_natCast]
    exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨hmem, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  have h0 := v.ord_coe_unit hunit.unit
  rw [IsUnit.unit_spec] at h0
  change v.ord f = 0 at h0
  omega

theorem exists_valuationSubring_algHom (t : M) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ M] [IsGalois K⟮t⟯ M]
    (W₀ : Place K M) (j₀ : K) (hW₀ : t - algebraMap K M j₀ ∈ W₀.toValuationSubring.nonunits)
    {Ω : Type*} [Field Ω] [Algebra K Ω] (W : Place K Ω) (j : Ω) (hj : Transcendental K j)
    (hjW : j - algebraMap K Ω j₀ ∈ W.toValuationSubring.nonunits)
    (Ω' : Type*) [Field Ω'] [IsAlgClosed Ω'] [Algebra K Ω'] [Algebra Ω Ω']
    [IsScalarTower K Ω Ω'] :
    ∃ (O : ValuationSubring Ω') (ι : M →ₐ[K] Ω'),
      (∀ a : Ω, algebraMap Ω Ω' a ∈ O ↔ a ∈ W.toValuationSubring) ∧
      ι t = algebraMap Ω Ω' j ∧
      ∀ m : M, ι m ∈ O ↔ m ∈ W₀.toValuationSubring := by

  obtain ⟨O, hO⟩ := exists_valuationSubring_over (Ω' := Ω') W.toValuationSubring
  set j' : Ω' := algebraMap Ω Ω' j with hj'def
  have hj' : Transcendental K j' := by
    intro halg
    exact hj ((isAlgebraic_algHom_iff (IsScalarTower.toAlgHom K Ω Ω')
      (algebraMap Ω Ω').injective).1 halg)
  have hπO : j' - algebraMap K Ω' j₀ ∈ O.nonunits := by
    have := mem_nonunits_of_over hO hjW
    rwa [map_sub, ← IsScalarTower.algebraMap_apply] at this
  have hπO0 : j' - algebraMap K Ω' j₀ ≠ 0 := fun h => by
    have : j' = algebraMap K Ω' j₀ := sub_eq_zero.1 h
    exact hj' (this ▸ isAlgebraic_algebraMap j₀)

  obtain ⟨f₀, hf₀⟩ := exists_algHom_adjoin_simple t ht j' hj'

  letI alg : Algebra K⟮t⟯ Ω' := f₀.toRingHom.toAlgebra
  have halg : ∀ x : K⟮t⟯, algebraMap K⟮t⟯ Ω' x = f₀ x := fun _ => rfl
  haveI : Algebra.IsAlgebraic K⟮t⟯ M := Algebra.IsAlgebraic.of_finite _ _
  haveI : Module.IsTorsionFree K⟮t⟯ Ω' := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree K⟮t⟯ M := DivisionSemiring.to_moduleIsTorsionFree
  let ι₀ : M →ₐ[K⟮t⟯] Ω' := IsAlgClosed.lift
  have hι₀K : ∀ c : K, ι₀ (algebraMap K M c) = algebraMap K Ω' c := by
    intro c
    rw [show algebraMap K M c = algebraMap K⟮t⟯ M (algebraMap K K⟮t⟯ c) from
      (IsScalarTower.algebraMap_apply K K⟮t⟯ M c), AlgHom.commutes, halg, AlgHom.commutes]
  let ι₀K : M →ₐ[K] Ω' := { ι₀.toRingHom with commutes' := hι₀K }
  have hι₀K_apply : ∀ m, ι₀K m = ι₀ m := fun _ => rfl
  have hgen : (t : M) = algebraMap K⟮t⟯ M (IntermediateField.AdjoinSimple.gen K t) := rfl
  have hι₀t : ι₀ t = j' := by
    have h1 : ι₀ (algebraMap K⟮t⟯ M (IntermediateField.AdjoinSimple.gen K t)) =
        algebraMap K⟮t⟯ Ω' (IntermediateField.AdjoinSimple.gen K t) :=
      AlgHom.commutes _ _
    rw [halg, hf₀] at h1
    exact h1

  haveI : Algebra.IsSeparable K⟮t⟯ M := IsGalois.to_isSeparable
  have hwK : ∀ a : K, ι₀K.toRingHom (algebraMap K M a) ∈ O := by
    intro a
    change ι₀K (algebraMap K M a) ∈ _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K Ω Ω', hO]
    exact W.algebraMap_mem' a
  have hwx : ∃ y : M, ι₀K.toRingHom y ∉ O := by
    refine ⟨(t - algebraMap K M j₀)⁻¹, ?_⟩
    change ι₀K _ ∉ _
    rw [map_inv₀, map_sub, AlgHom.commutes, hι₀K_apply, hι₀t]
    exact ((ValuationSubring.mem_nonunits_iff_or _).1 hπO).resolve_left hπO0
  obtain ⟨v, hv⟩ :=
    AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
      (K := K) t ι₀K.toRingHom O hwK hwx
  have hvmem : ∀ m : M, m ∈ v.toValuationSubring ↔ ι₀ m ∈ O := by
    intro m; rw [hv]; rfl

  have hπv : t - algebraMap K M j₀ ∈ v.toValuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    rw [hvmem, map_inv₀, map_sub, hι₀t]
    have : ι₀ (algebraMap K M j₀) = algebraMap K Ω' j₀ := by
      rw [← hι₀K_apply, AlgHom.commutes]
    rw [this]
    exact ((ValuationSubring.mem_nonunits_iff_or _).1 hπO).resolve_left hπO0
  have hres : W₀.restrict K⟮t⟯ = v.restrict K⟮t⟯ := by
    apply Place.ext
    ext x
    rw [Place.restrict_toValuationSubring, Place.restrict_toValuationSubring,
      ValuationSubring.mem_comap, ValuationSubring.mem_comap]
    exact mem_iff_mem_of_sub_mem_nonunits t ht j₀ _ _ W₀.algebraMap_mem' v.algebraMap_mem' hW₀ hπv
      _ (x.2)

  obtain ⟨σ, hσ⟩ := AlgebraicCurve.Place.exists_algEquiv_smul_eq_of_restrict_eq (K := K)
    (F' := K⟮t⟯) v W₀ hres

  let ι : M →ₐ[K] Ω' := ι₀K.comp (σ.symm.restrictScalars K : M →ₐ[K] M)
  refine ⟨O, ι, hO, ?_, ?_⟩
  · change ι₀ (σ.symm t) = j'
    have h1 : σ.symm (algebraMap K⟮t⟯ M (IntermediateField.AdjoinSimple.gen K t)) =
        algebraMap K⟮t⟯ M (IntermediateField.AdjoinSimple.gen K t) := AlgEquiv.commutes _ _
    rw [← hgen] at h1
    rw [h1, hι₀t]
  · intro m
    change ι₀ (σ.symm m) ∈ O ↔ _
    rw [← hvmem, ← hσ]
    change _ ↔ m ∈ (SemilinearAut.ofAlgAut (σ.restrictScalars K)) • v.toValuationSubring
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl

end Main

end PlaceRealisation
end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_exists_valuationSubring_algHom_apply_eq_forall_mem_iff.AlgebraicCurve in
open scoped IntermediateField in
universe u v w x in
theorem solution
    {K : Type u} [Field K] {M : Type v} [Field M] [Algebra K M]
    (t : M) (ht : Transcendental K t) [FiniteDimensional K⟮t⟯ M] [IsGalois K⟮t⟯ M]
    (W₀ : Place K M) (j₀ : K) (hW₀ : t - algebraMap K M j₀ ∈ W₀.toValuationSubring.nonunits)
    {Ω : Type w} [Field Ω] [Algebra K Ω] (W : Place K Ω) (j : Ω) (hj : Transcendental K j)
    (hjW : j - algebraMap K Ω j₀ ∈ W.toValuationSubring.nonunits)
    (Ω' : Type x) [Field Ω'] [IsAlgClosed Ω'] [Algebra K Ω'] [Algebra Ω Ω']
    [IsScalarTower K Ω Ω'] :
    ∃ (O : ValuationSubring Ω') (ι : M →ₐ[K] Ω'),
      (∀ a : Ω, algebraMap Ω Ω' a ∈ O ↔ a ∈ W.toValuationSubring) ∧
      ι t = algebraMap Ω Ω' j ∧
      ∀ m : M, ι m ∈ O ↔ m ∈ W₀.toValuationSubring :=
  AlgebraicCurve.PlaceRealisation.exists_valuationSubring_algHom t ht W₀ j₀ hW₀ W j hj hjW Ω'

end S_AlgebraicCurve_Place_exists_valuationSubring_algHom_apply_eq_forall_mem_iff
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_valuationSubring_algHom_apply_eq_forall_mem_iff (solution)
