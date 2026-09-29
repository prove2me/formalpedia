-- Prove2me | solution 1 for ArtinL.conductorExponent_add_finrank_inertiaInvariants_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/384fa652-40b2-5290-871c-d2400a7a1d1d

import Mathlib
import Definitions.Def_ArtinL_Conductor
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_IsLocalRing_pow_mem_lowerRamificationGroup_succ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_conductorExponent_add_finrank_inertiaInvariants_eq

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups Pointwise NumberField
open Polynomial

namespace ArtinLTame

section Places

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem mem_decompositionSubgroup_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ A.decompositionSubgroup K ↔ σ • A = A := MulAction.mem_stabilizer_iff

theorem residue_eq_iff (A : ValuationSubring L) (a b : A) :
    IsLocalRing.residue A a = IsLocalRing.residue A b ↔ ((a : L) - b) ∈ A.nonunits := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

theorem mem_inertiaSubgroupIn_iff (A : ValuationSubring L) (τ : L ≃ₐ[K] L) :
    τ ∈ A.inertiaSubgroupIn K ↔ τ • A = A ∧ ∀ a ∈ A, τ a - a ∈ A.nonunits := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨(mem_decompositionSubgroup_iff A _).1 d.2, fun a ha => ?_⟩
    have hker : ∀ x : IsLocalRing.ResidueField A, d • x = x := fun x => by
      have := RingEquiv.congr_fun (MonoidHom.mem_ker.1 hd) x
      simpa using this
    have h1 := hker (IsLocalRing.residue A ⟨a, ha⟩)
    rw [← IsLocalRing.ResidueField.residue_smul, residue_eq_iff] at h1
    simp at h1
    exact h1
  · rintro ⟨hτ, h⟩
    have hτ' : τ ∈ A.decompositionSubgroup K := (mem_decompositionSubgroup_iff A τ).2 hτ
    refine ⟨⟨τ, hτ'⟩, ?_, rfl⟩
    simp only [ValuationSubring.inertiaSubgroup, SetLike.mem_coe, MonoidHom.mem_ker]
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change (⟨τ, hτ'⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, residue_eq_iff]
    exact h a a.2

theorem mem_smul_iff (g : L ≃ₐ[K] L) (A : ValuationSubring L) (x : L) :
    x ∈ g • A ↔ g⁻¹ x ∈ A :=
  ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem

theorem mem_nonunits_smul_iff (g : L ≃ₐ[K] L) (A : ValuationSubring L) (x : L) :
    x ∈ (g • A).nonunits ↔ g⁻¹ x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    mem_smul_iff, map_inv₀, EmbeddingLike.map_eq_zero_iff]

theorem conj_mem_inertiaSubgroupIn {A : ValuationSubring L} {τ : L ≃ₐ[K] L}
    (h : τ ∈ A.inertiaSubgroupIn K) (g : L ≃ₐ[K] L) :
    g * τ * g⁻¹ ∈ (g • A).inertiaSubgroupIn K := by
  rw [mem_inertiaSubgroupIn_iff] at h ⊢
  obtain ⟨hτ, h⟩ := h
  refine ⟨by rw [mul_smul, mul_smul, inv_smul_smul, hτ], fun x hx => ?_⟩
  rw [mem_nonunits_smul_iff, map_sub]
  have hx' : g⁻¹ x ∈ A := (mem_smul_iff g A x).1 hx
  have := h _ hx'
  simpa [AlgEquiv.aut_mul, AlgEquiv.aut_inv, AlgEquiv.mul_apply] using this

theorem inv_conj_mem_inertiaSubgroupIn {A : ValuationSubring L} {τ : L ≃ₐ[K] L} (g : L ≃ₐ[K] L)
    (h : τ ∈ (g • A).inertiaSubgroupIn K) : g⁻¹ * τ * g ∈ A.inertiaSubgroupIn K := by
  have := conj_mem_inertiaSubgroupIn h g⁻¹
  rwa [inv_smul_smul, inv_inv] at this

theorem inertiaSubgroupIn_smul (A : ValuationSubring L) (g : L ≃ₐ[K] L) :
    (g • A).inertiaSubgroupIn K = (A.inertiaSubgroupIn K).map (MulAut.conj g).toMonoidHom := by
  ext τ
  rw [Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨g⁻¹ * τ * g, inv_conj_mem_inertiaSubgroupIn g h, by simp [MulAut.conj_apply]; group⟩
  · rintro ⟨τ', hτ', rfl⟩
    exact conj_mem_inertiaSubgroupIn hτ' g

end Places

section Rep

variable {n : ℕ}

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "ℚbar" => AlgebraicClosure ℚ

variable (ρ : Γℚ →* GL (Fin n) ℂ)

abbrev π : Representation ℂ Γℚ (Fin n → ℂ) := Deformation.matrixRepresentation ρ

theorem mem_invariantsUnder_iff (H : Subgroup Γℚ) (v : Fin n → ℂ) :
    v ∈ ArtinL.invariantsUnder ρ H ↔ ∀ τ ∈ H, π ρ τ v = v := by
  rw [ArtinL.invariantsUnder, Representation.mem_invariants]
  exact ⟨fun h τ hτ => h ⟨τ, hτ⟩, fun h τ => h τ τ.2⟩

theorem π_mul_apply (σ τ : Γℚ) (v : Fin n → ℂ) : π ρ (σ * τ) v = π ρ σ (π ρ τ v) := by
  rw [map_mul]; rfl

theorem π_eq_one_of {σ : Γℚ} (h : ρ σ = 1) (v : Fin n → ℂ) : π ρ σ v = v := by
  simp [Deformation.matrixRepresentation_apply, h]

theorem apply_mem_inertiaInvariants_smul (A : ValuationSubring ℚbar) (g : Γℚ) {v : Fin n → ℂ}
    (hv : v ∈ ArtinL.inertiaInvariants ρ A) : π ρ g v ∈ ArtinL.inertiaInvariants ρ (g • A) := by
  rw [ArtinL.inertiaInvariants, mem_invariantsUnder_iff] at hv ⊢
  intro τ hτ
  have hτ' := inv_conj_mem_inertiaSubgroupIn g hτ
  have := hv _ hτ'
  calc π ρ τ (π ρ g v) = π ρ (g * (g⁻¹ * τ * g)) v := by
          rw [← π_mul_apply]; congr 1; group
    _ = π ρ g v := by rw [π_mul_apply, this]

def πEquiv (g : Γℚ) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofLinear (π ρ g) (π ρ g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem map_inertiaInvariants (A : ValuationSubring ℚbar) (g : Γℚ) :
    (ArtinL.inertiaInvariants ρ A).map (πEquiv ρ g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) =
      ArtinL.inertiaInvariants ρ (g • A) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact apply_mem_inertiaInvariants_smul ρ A g hv
  · intro w hw
    refine ⟨π ρ g⁻¹ w, ?_, ?_⟩
    · have := apply_mem_inertiaInvariants_smul ρ (g • A) g⁻¹ hw
      rwa [inv_smul_smul] at this
    · change π ρ g (π ρ g⁻¹ w) = w
      rw [← π_mul_apply, mul_inv_cancel, map_one]; rfl

def invEquiv (A : ValuationSubring ℚbar) (g : Γℚ) :
    ArtinL.inertiaInvariants ρ A ≃ₗ[ℂ] ArtinL.inertiaInvariants ρ (g • A) :=
  LinearEquiv.ofSubmodules (πEquiv ρ g) _ _ (map_inertiaInvariants ρ A g)

theorem finrank_inertiaInvariants_smul (A : ValuationSubring ℚbar) (g : Γℚ) :
    Module.finrank ℂ (ArtinL.inertiaInvariants ρ (g • A)) =
      Module.finrank ℂ (ArtinL.inertiaInvariants ρ A) :=
  (invEquiv ρ A g).finrank_eq.symm

theorem finrank_inertiaInvariants_le (A : ValuationSubring ℚbar) :
    Module.finrank ℂ (ArtinL.inertiaInvariants ρ A) ≤ n := by
  simpa using Submodule.finrank_le (ArtinL.inertiaInvariants ρ A)

theorem card_map_inertia_smul (A : ValuationSubring ℚbar) (g : Γℚ) :
    Nat.card (((g • A).inertiaSubgroupIn ℚ).map ρ) = Nat.card ((A.inertiaSubgroupIn ℚ).map ρ) := by
  rw [inertiaSubgroupIn_smul, Subgroup.map_map]
  have hcomp : ρ.comp (MulAut.conj g).toMonoidHom = (MulAut.conj (ρ g)).toMonoidHom.comp ρ := by
    ext1 τ; simp [MulAut.conj_apply]
  rw [hcomp, ← Subgroup.map_map]
  exact Nat.card_congr
    (((A.inertiaSubgroupIn ℚ).map ρ).equivMapOfInjective _ (MulAut.conj (ρ g)).injective).toEquiv.symm

theorem invariantsUnder_eq_top_of_le_ker {H : Subgroup Γℚ} (h : H ≤ ρ.ker) :
    ArtinL.invariantsUnder ρ H = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [mem_invariantsUnder_iff]
  intro τ hτ
  exact π_eq_one_of ρ (MonoidHom.mem_ker.1 (h hτ)) v

theorem codimInvariants_eq_zero_of_le_ker {H : Subgroup Γℚ} (h : H ≤ ρ.ker) :
    ArtinL.codimInvariants ρ H = 0 := by
  rw [ArtinL.codimInvariants, invariantsUnder_eq_top_of_le_ker ρ h, finrank_top,
    Module.finrank_fin_fun, Nat.sub_self]

end Rep

section Level

variable {n : ℕ}

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "ℚbar" => AlgebraicClosure ℚ

local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

variable (ρ : Γℚ →* GL (Fin n) ℂ)

theorem smul_eq_of_mem_ker {σ : Γℚ} (hσ : σ ∈ ρ.ker) (x : ArtinL.splittingField ρ) : σ • x = x := by
  apply Subtype.ext
  rw [ArtinL.coe_smul_splittingField]
  exact (IntermediateField.mem_fixedField_iff ρ.ker (x : ℚbar)).1 x.2 σ hσ

theorem isOpen_ker (hρ : GaloisFactorsThroughFiniteLevel ρ) : IsOpen (ρ.ker : Set Γℚ) := by
  obtain ⟨L, hL, hker⟩ := hρ
  haveI := hL
  refine Subgroup.isOpen_mono (H₁ := L.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen L)
  intro σ hσ
  rw [MonoidHom.mem_ker]
  exact hker σ (fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx)

theorem isClosed_ker (hρ : GaloisFactorsThroughFiniteLevel ρ) : IsClosed (ρ.ker : Set Γℚ) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_ker ρ hρ)

theorem mem_ker_of_forall_smul_eq (hρ : GaloisFactorsThroughFiniteLevel ρ) {σ : Γℚ}
    (h : ∀ x : ArtinL.splittingField ρ, σ • x = x) : σ ∈ ρ.ker := by
  have hfix : σ ∈ (IntermediateField.fixedField (F := ℚ) (E := ℚbar) ρ.ker).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have := congrArg (fun y : ArtinL.splittingField ρ => (y : ℚbar)) (h ⟨x, hx⟩)
    simpa using this
  have key := InfiniteGalois.fixingSubgroup_fixedField (⟨ρ.ker, isClosed_ker ρ hρ⟩ : ClosedSubgroup Γℚ)
  change (IntermediateField.fixedField ρ.ker).fixingSubgroup = ρ.ker at key
  rwa [key] at hfix

theorem finiteDimensional_splittingField (hρ : GaloisFactorsThroughFiniteLevel ρ) :
    FiniteDimensional ℚ (ArtinL.splittingField ρ) := by
  obtain ⟨L, hL, hker⟩ := hρ
  haveI := hL
  have hle : ArtinL.splittingField ρ ≤ L := by
    have h1 : L.fixingSubgroup ≤ ρ.ker := fun σ hσ =>
      (MonoidHom.mem_ker).2 (hker σ fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx)
    have h2 := IntermediateField.fixedField_antitone (F := ℚ) (E := ℚbar) h1
    rwa [InfiniteGalois.fixedField_fixingSubgroup] at h2
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).injective

theorem finite_range (hρ : GaloisFactorsThroughFiniteLevel ρ) : Finite ρ.range := by
  obtain ⟨L, hL, hker⟩ := hρ
  haveI := hL

  have hopen : IsOpen (ρ.ker : Set Γℚ) := isOpen_ker ρ ⟨L, hL, hker⟩
  have : Finite (Γℚ ⧸ ρ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv

end Level

section DVR

variable {F : Type*} [Field F]

theorem coe_ringOfIntegers_mem (R : ValuationSubring F) (a : 𝓞 F) : (a : F) ∈ R := by
  have hint : IsIntegral R (a : F) := by
    have h : IsIntegral ℤ (a : F) := a.isIntegral_coe
    exact h.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := F)).1 hint
  rw [← hy]; exact y.2

def intToR (R : ValuationSubring F) : 𝓞 F →+* R :=
  (algebraMap (𝓞 F) F).codRestrict R.toSubring (coe_ringOfIntegers_mem R)

@[scoped simp] theorem coe_intToR (R : ValuationSubring F) (a : 𝓞 F) : ((intToR R a : R) : F) = a := rfl

def primeBelow (R : ValuationSubring F) : Ideal (𝓞 F) :=
  (IsLocalRing.maximalIdeal R).comap (intToR R)

scoped instance (R : ValuationSubring F) : (primeBelow R).IsPrime :=
  Ideal.comap_isPrime _ _

theorem mem_primeBelow_iff (R : ValuationSubring F) (a : 𝓞 F) :
    a ∈ primeBelow R ↔ (a : F) ∈ R.nonunits := by
  rw [primeBelow, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff, coe_intToR]

variable [NumberField F]

theorem primeBelow_ne_bot (R : ValuationSubring F) {p : ℕ} (hp : p.Prime)
    (hpR : (p : F) ∈ R.nonunits) : primeBelow R ≠ ⊥ := by
  intro h
  have hmem : ((p : ℕ) : 𝓞 F) ∈ primeBelow R := by
    rw [mem_primeBelow_iff]; simpa using hpR
  rw [h, Ideal.mem_bot] at hmem
  exact (Nat.cast_ne_zero.2 hp.ne_zero) hmem

def loc (R : ValuationSubring F) : Subalgebra (𝓞 F) F :=
  Localization.subalgebra.ofField F (primeBelow R).primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

theorem mem_loc_iff (R : ValuationSubring F) (x : F) :
    x ∈ loc R ↔ ∃ a s : 𝓞 F, s ∉ primeBelow R ∧ x = (a : F) * ((s : F))⁻¹ := by
  change x ∈ {x : F | ∃ (a s : 𝓞 F) (_ : s ∈ (primeBelow R).primeCompl),
    x = algebraMap (𝓞 F) F a * (algebraMap (𝓞 F) F s)⁻¹} ↔ _
  simp only [Set.mem_setOf_eq, Ideal.mem_primeCompl_iff, exists_prop]

scoped instance (R : ValuationSubring F) : IsLocalization.AtPrime (loc R) (primeBelow R) :=
  Localization.subalgebra.isLocalization_ofField F _ _

omit [NumberField F] in

theorem inv_mem_of_not_mem_nonunits (R : ValuationSubring F) {x : F} (hx : x ∉ R.nonunits) :
    x⁻¹ ∈ R := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hx
  exact hx.2

theorem loc_le (R : ValuationSubring F) {x : F} (hx : x ∈ loc R) : x ∈ R := by
  obtain ⟨a, s, hs, rfl⟩ := (mem_loc_iff R x).1 hx
  rw [mem_primeBelow_iff] at hs
  exact R.mul_mem _ _ (coe_ringOfIntegers_mem R a) (inv_mem_of_not_mem_nonunits R hs)

omit [NumberField F] in
theorem mul_mem_nonunits (R : ValuationSubring F) {x y : F} (hx : x ∈ R.nonunits) (hy : y ∈ R) :
    x * y ∈ R.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [map_mul]
  exact mul_lt_one_of_lt_of_le hx ((R.valuation_le_one_iff y).2 hy)

theorem le_loc (R : ValuationSubring F) {p : ℕ} (hp : p.Prime) (hpR : (p : F) ∈ R.nonunits)
    {x : F} (hx : x ∈ R) : x ∈ loc R := by
  have hne := primeBelow_ne_bot R hp hpR
  haveI : IsDiscreteValuationRing (loc R) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) hne (loc R)
  rcases ValuationRing.isInteger_or_isInteger (loc R) x with ⟨v, hv⟩ | ⟨v, hv⟩
  · rw [← hv]; exact v.2
  ·
    have hxinv : x⁻¹ ∈ loc R := by rw [← hv]; exact v.2
    obtain ⟨a, s, hs, hxs⟩ := (mem_loc_iff R _).1 hxinv
    by_cases ha : a ∈ primeBelow R
    ·
      rw [mem_primeBelow_iff] at ha
      rw [mem_primeBelow_iff] at hs
      have h1 : x⁻¹ ∈ R.nonunits := by
        rw [hxs]; exact mul_mem_nonunits R ha (inv_mem_of_not_mem_nonunits R hs)
      by_cases hx0 : x = 0
      · rw [hx0]; exact Subalgebra.zero_mem _
      · exfalso
        rw [ValuationSubring.mem_nonunits_iff] at h1
        have h2 := (R.valuation_le_one_iff x).2 hx
        have : R.valuation (x⁻¹ * x) < 1 := by
          rw [map_mul]; exact mul_lt_one_of_lt_of_le h1 h2
        rw [inv_mul_cancel₀ hx0, map_one] at this
        exact lt_irrefl _ this
    ·
      rw [mem_loc_iff]
      refine ⟨s, a, ha, ?_⟩
      have := congrArg (fun y : F => y⁻¹) hxs
      simpa [mul_inv, mul_comm] using this

theorem toSubring_eq_loc (R : ValuationSubring F) {p : ℕ} (hp : p.Prime)
    (hpR : (p : F) ∈ R.nonunits) : R.toSubring = (loc R).toSubring := by
  ext x
  exact ⟨fun hx => le_loc R hp hpR hx, fun hx => loc_le R hx⟩

theorem isNoetherianRing_of_mem_nonunits (R : ValuationSubring F) {p : ℕ} (hp : p.Prime)
    (hpR : (p : F) ∈ R.nonunits) : IsNoetherianRing R := by
  haveI : IsNoetherianRing (loc R) :=
    IsLocalization.isNoetherianRing (primeBelow R).primeCompl (loc R) inferInstance
  exact isNoetherianRing_of_ringEquiv (loc R) (RingEquiv.subringCongr (toSubring_eq_loc R hp hpR)).symm

theorem iInf_pow_maximalIdeal_eq_bot (R : ValuationSubring F) {p : ℕ} (hp : p.Prime)
    (hpR : (p : F) ∈ R.nonunits) : ⨅ i : ℕ, IsLocalRing.maximalIdeal R ^ i = ⊥ := by
  haveI := isNoetherianRing_of_mem_nonunits R hp hpR
  exact Ideal.iInf_pow_eq_bot_of_isDomain _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top

end DVR

section Wild

variable {n : ℕ}

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "ℚbar" => AlgebraicClosure ℚ

local instance isAlgebraicQbar' : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar' : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance isGaloisQbar' : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

variable (ρ : Γℚ →* GL (Fin n) ℂ)

theorem numberField_splittingField (hρ : GaloisFactorsThroughFiniteLevel ρ) :
    NumberField (ArtinL.splittingField ρ) := by
  have hfd := finiteDimensional_splittingField ρ hρ
  have halg : (DivisionRing.toRatAlgebra : Algebra ℚ (ArtinL.splittingField ρ)) =
      (ArtinL.splittingField ρ).algebra := Subsingleton.elim _ _
  haveI hFD : @FiniteDimensional ℚ (ArtinL.splittingField ρ) _ _
      DivisionRing.toRatAlgebra.toModule := by
    rw [halg]; exact hfd
  exact @NumberField.mk _ _ inferInstance hFD

theorem mem_nonunits_placeUnder_iff (A : ValuationSubring ℚbar) (x : ArtinL.splittingField ρ) :
    x ∈ (ArtinL.placeUnder ρ A).nonunits ↔ (x : ℚbar) ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ArtinL.mem_placeUnder_iff]
  simp

theorem natCast_mem_nonunits_placeUnder {A : ValuationSubring ℚbar} {p : ℕ} (hA : A.LiesOverPrime p) :
    ((p : ArtinL.splittingField ρ)) ∈ (ArtinL.placeUnder ρ A).nonunits := by
  rw [mem_nonunits_placeUnder_iff]
  simp at hA ⊢
  exact hA

theorem natCast_mem_maximalIdeal_placeUnder {A : ValuationSubring ℚbar} {p : ℕ}
    (hA : A.LiesOverPrime p) :
    ((p : ArtinL.placeUnder ρ A)) ∈ IsLocalRing.maximalIdeal (ArtinL.placeUnder ρ A) := by
  rw [← ValuationSubring.coe_mem_nonunits_iff]
  simpa using natCast_mem_nonunits_placeUnder ρ hA

theorem pow_prime_pow_mem {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G]
    [MulSemiringAction G R] {p : ℕ} (hp : (p : R) ∈ IsLocalRing.maximalIdeal R) {e : G}
    (he : e ∈ IsLocalRing.lowerRamificationGroup R G 1) (k : ℕ) :
    e ^ p ^ k ∈ IsLocalRing.lowerRamificationGroup R G (k + 1) := by
  induction k with
  | zero => simpa using he
  | succ k ih =>
    rw [pow_succ, pow_mul]
    exact IsLocalRing.pow_mem_lowerRamificationGroup_succ hp (Nat.succ_le_succ (Nat.zero_le k)) ih

theorem smul_placeUnder_eq_of_mem_ker (A : ValuationSubring ℚbar) {u : A.decompositionSubgroup ℚ}
    (hu : (u : Γℚ) ∈ ρ.ker) (r : ArtinL.placeUnder ρ A) : u • r = r := by
  apply Subtype.ext
  change (u : Γℚ) • (r : ArtinL.splittingField ρ) = r
  exact smul_eq_of_mem_ker ρ hu _

theorem smul_splittingField_eq_of_forall (A : ValuationSubring ℚbar) {d : A.decompositionSubgroup ℚ}
    (hd : ∀ r : ArtinL.placeUnder ρ A, d • r = r) (x : ArtinL.splittingField ρ) :
    (d : Γℚ) • x = x := by
  rcases A.mem_or_inv_mem (x : ℚbar) with hx | hx
  · have := hd ⟨x, (ArtinL.mem_placeUnder_iff ρ A x).2 hx⟩
    exact congrArg (fun r : ArtinL.placeUnder ρ A => (r : ArtinL.splittingField ρ)) this
  · have hx' : x⁻¹ ∈ ArtinL.placeUnder ρ A := by
      rw [ArtinL.mem_placeUnder_iff]; simpa using hx
    have := hd ⟨x⁻¹, hx'⟩
    have h2 : (d : Γℚ) • x⁻¹ = x⁻¹ :=
      congrArg (fun r : ArtinL.placeUnder ρ A => (r : ArtinL.splittingField ρ)) this
    rw [smul_inv''] at h2
    exact inv_injective h2

theorem ramificationGroup_succ_le_ker (hρ : GaloisFactorsThroughFiniteLevel ρ) {p : ℕ}
    (hp : p.Prime) (A : ValuationSubring ℚbar) (hA : A.LiesOverPrime p)
    (htame : (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ)).Coprime p) (i : ℕ) :
    ArtinL.ramificationGroup ρ A (i + 1) ≤ ρ.ker := by
  haveI := numberField_splittingField ρ hρ

  set R := ArtinL.placeUnder ρ A with hR
  set H := (A.inertiaSubgroupIn ℚ).map ρ with hH
  have hpR : ((p : R)) ∈ IsLocalRing.maximalIdeal R := natCast_mem_maximalIdeal_placeUnder ρ hA
  have hpR' : ((p : ArtinL.splittingField ρ)) ∈ R.nonunits := natCast_mem_nonunits_placeUnder ρ hA
  have hKrull := iInf_pow_maximalIdeal_eq_bot R hp hpR'

  have hc0 : Nat.card H ≠ 0 := by
    intro h0
    rw [h0, Nat.coprime_zero_left] at htame
    exact hp.one_lt.ne' htame
  haveI : Finite H := Nat.finite_of_card_ne_zero hc0
  intro σ hσ
  obtain ⟨hσI, hσG⟩ := Subgroup.mem_inf.1 hσ
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hσG
  change (d : Γℚ) ∈ A.inertiaSubgroupIn ℚ at hσI
  have hd1 : d ∈ IsLocalRing.lowerRamificationGroup R (A.decompositionSubgroup ℚ) 1 :=
    IsLocalRing.lowerRamificationGroup_antitone (Nat.succ_le_succ (Nat.zero_le i)) hd

  have hx : ρ (d : Γℚ) ∈ H := Subgroup.mem_map_of_mem ρ hσI
  have hxc : ρ (d : Γℚ) ^ Nat.card H = 1 := by
    have := pow_card_eq_one' (G := H) (x := ⟨ρ (d : Γℚ), hx⟩)
    exact congrArg Subtype.val this

  have hall : ∀ k : ℕ, d ∈ IsLocalRing.lowerRamificationGroup R (A.decompositionSubgroup ℚ) (k + 1) := by
    intro k

    obtain ⟨m, hm⟩ : ∃ m : ℕ, ρ (d : Γℚ) ^ (p ^ k * m) = ρ (d : Γℚ) := by
      by_cases hc1 : Nat.card H = 1
      · refine ⟨1, ?_⟩
        have hbot : H = ⊥ := Subgroup.card_eq_one.1 hc1
        have : ρ (d : Γℚ) = 1 := by rw [hbot] at hx; exact Subgroup.mem_bot.1 hx
        simp [this]
      · have hlt : 1 < Nat.card H := lt_of_le_of_ne (Nat.one_le_iff_ne_zero.2 hc0) (Ne.symm hc1)
        obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
          (Nat.Coprime.pow_right k htame).symm hlt
        refine ⟨m, ?_⟩
        conv_lhs => rw [← Nat.div_add_mod (p ^ k * m) (Nat.card H), hm, pow_add, pow_mul, hxc,
          one_pow, one_mul, pow_one]

    have hd' : d ^ m ∈ IsLocalRing.lowerRamificationGroup R (A.decompositionSubgroup ℚ) 1 :=
      Subgroup.pow_mem _ hd1 m
    have hdk := pow_prime_pow_mem hpR hd' k
    rw [← pow_mul, mul_comm] at hdk
    set e := d ^ (p ^ k * m) with he
    have hu : (((e⁻¹ * d : A.decompositionSubgroup ℚ)) : Γℚ) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, he,
        Subgroup.coe_pow, map_pow, hm, inv_mul_cancel]
    rw [IsLocalRing.mem_lowerRamificationGroup] at hdk ⊢
    intro r
    have hfix := smul_placeUnder_eq_of_mem_ker ρ A hu r
    have : d • r = e • r := by
      conv_lhs => rw [show d = e * (e⁻¹ * d) by group, mul_smul, hfix]
    rw [this]
    exact hdk r

  have hfixR : ∀ r : R, d • r = r := by
    intro r
    have hmem : d • r - r ∈ ⨅ i : ℕ, IsLocalRing.maximalIdeal R ^ i := by
      rw [Ideal.mem_iInf]
      intro i
      exact Ideal.pow_le_pow_right (by omega : i ≤ i + 1 + 1)
        ((IsLocalRing.mem_lowerRamificationGroup.1 (hall i)) r)
    rw [hKrull, Ideal.mem_bot, sub_eq_zero] at hmem
    exact hmem
  exact mem_ker_of_forall_smul_eq ρ hρ (smul_splittingField_eq_of_forall ρ A hfixR)

theorem swanConductor_eq_zero (hρ : GaloisFactorsThroughFiniteLevel ρ) {p : ℕ}
    (hp : p.Prime) (A : ValuationSubring ℚbar) (hA : A.LiesOverPrime p)
    (htame : (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ)).Coprime p) :
    ArtinL.swanConductor ρ A = 0 := by
  rw [ArtinL.swanConductor]
  apply finsum_eq_zero_of_forall_eq_zero
  intro i
  rw [codimInvariants_eq_zero_of_le_ker ρ (ramificationGroup_succ_le_ker ρ hρ hp A hA htame i),
    Nat.cast_zero, mul_zero]

theorem conductorExponentAt_eq (hρ : GaloisFactorsThroughFiniteLevel ρ) {p : ℕ}
    (hp : p.Prime) (A : ValuationSubring ℚbar) (hA : A.LiesOverPrime p)
    (htame : (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ)).Coprime p) :
    ArtinL.conductorExponentAt ρ A = n - Module.finrank ℂ (ArtinL.inertiaInvariants ρ A) := by
  rw [ArtinL.conductorExponentAt, swanConductor_eq_zero ρ hρ hp A hA htame, Nat.ceil_zero,
    add_zero, ArtinL.codimInvariants]

end Wild

end ArtinLTame
p2m_reactivate "P2MW.S_ArtinL_conductorExponent_add_finrank_inertiaInvariants_eq.ArtinLTame"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open ArtinLTame in
theorem solution {n : ℕ}
    (ρ : Γℚ →* GL (Fin n) ℂ) (hρ : GaloisFactorsThroughFiniteLevel ρ)
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (htame : (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ)).Coprime p) :
    ArtinL.conductorExponent ρ p + Module.finrank ℂ (ArtinL.inertiaInvariants ρ A) = n := by
  have hex : p.Prime ∧ ∃ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime p :=
    ⟨hp, A, hA⟩
  rw [ArtinL.conductorExponent, dif_pos hex]
  have hA₀ : hex.2.choose.LiesOverPrime p := hex.2.choose_spec
  obtain ⟨g, hg⟩ :=
    ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime hp A hex.2.choose hA hA₀
  have htame₀ : (Nat.card (((hex.2.choose).inertiaSubgroupIn ℚ).map ρ)).Coprime p := by
    rw [← hg, card_map_inertia_smul]; exact htame
  rw [conductorExponentAt_eq ρ hρ hp _ hA₀ htame₀, ← hg, finrank_inertiaInvariants_smul]
  have := finrank_inertiaInvariants_le ρ A
  omega

end
p2m_reactivate "P2MW.S_ArtinL_conductorExponent_add_finrank_inertiaInvariants_eq.ArtinLTame"

end S_ArtinL_conductorExponent_add_finrank_inertiaInvariants_eq
end P2MW
export P2MW.S_ArtinL_conductorExponent_add_finrank_inertiaInvariants_eq (solution)
