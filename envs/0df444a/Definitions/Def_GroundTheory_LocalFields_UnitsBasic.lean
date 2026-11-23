-- Prove2me | Definitions.Def_GroundTheory_LocalFields_UnitsBasic
-- name    : GroundTheory_LocalFields_UnitsBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:56.698672+00:00
-- url     : https://prove2.me/theorems/ded3aa25-203b-4362-8f74-dde6ee7929be
-- title:
--   Units Basic
-- statement:
--   Definitions and structural lemmas for Units Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField
open ValuativeRel IsLocalRing
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section Filtration
def unitFiltration (n : ℕ) : Subgroup 𝒪[K]ˣ where
  carrier := {u | (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ n}
  one_mem' := by simp
  mul_mem' {u w} hu hw := by
    have h : ((u * w : 𝒪[K]ˣ) : 𝒪[K]) - 1 =
        (u : 𝒪[K]) * ((w : 𝒪[K]) - 1) + ((u : 𝒪[K]) - 1) := by
      push_cast; ring
    simp only [Set.mem_ofPred_eq] at hu hw ⊢
    rw [h]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hw) hu
  inv_mem' {u} hu := by
    have h : ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1 = -((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * ((u : 𝒪[K]) - 1) := by
      linear_combination (u.inv_mul)
    simp only [Set.mem_ofPred_eq] at hu ⊢
    rw [h]
    exact Ideal.mul_mem_left _ _ hu
variable {K} in
theorem mem_unitFiltration {n : ℕ} {u : 𝒪[K]ˣ} :
    u ∈ unitFiltration K n ↔ (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ n := Iff.rfl
@[simp]
theorem unitFiltration_zero : unitFiltration K 0 = ⊤ := by
  ext u; simp [mem_unitFiltration]
theorem unitFiltration_antitone : Antitone (unitFiltration K) :=
  fun _ _ hmn _ hu ↦ Ideal.pow_le_pow_right hmn hu
theorem unitFiltration_succ_le (n : ℕ) : unitFiltration K (n + 1) ≤ unitFiltration K n :=
  unitFiltration_antitone K n.le_succ
end Filtration
section Uniformizer
variable {K}
theorem mem_maximalIdeal_pow_iff {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n : ℕ} {x : 𝒪[K]} :
    x ∈ 𝓂[K] ^ n ↔ ϖ ^ n ∣ x := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
theorem mem_maximalIdeal_iff_dvd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {x : 𝒪[K]} :
    x ∈ 𝓂[K] ↔ ϖ ∣ x := by
  simpa using mem_maximalIdeal_pow_iff hϖ (n := 1) (x := x)
theorem uniformizer_mem_maximalIdeal {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) : ϖ ∈ 𝓂[K] :=
  (mem_maximalIdeal_iff_dvd hϖ).mpr dvd_rfl
theorem residue_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) : residue 𝒪[K] ϖ = 0 :=
  (residue_eq_zero_iff _).mpr (uniformizer_mem_maximalIdeal hϖ)
end Uniformizer
section Valuation
noncomputable def normalizedValuation : Valuation K ℤᵐ⁰ :=
  (valuation K).map
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMulEquiv.toMonoidWithZeroHom
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.monotone
variable {K}
theorem normalizedValuation_apply (x : K) :
    normalizedValuation K x = IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K x) := by
  simp [normalizedValuation, Valuation.map_apply]
theorem normalizedValuation_le_iff {x y : K} :
    normalizedValuation K x ≤ normalizedValuation K y ↔ valuation K x ≤ valuation K y := by
  rw [normalizedValuation_apply, normalizedValuation_apply]
  exact map_le_map_iff _
theorem normalizedValuation_lt_iff {x y : K} :
    normalizedValuation K x < normalizedValuation K y ↔ valuation K x < valuation K y := by
  rw [normalizedValuation_apply, normalizedValuation_apply]
  exact map_lt_map_iff _
theorem normalizedValuation_eq_iff {x y : K} :
    normalizedValuation K x = normalizedValuation K y ↔ valuation K x = valuation K y := by
  rw [normalizedValuation_apply, normalizedValuation_apply]
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective.eq_iff
theorem valuation_unit (u : 𝒪[K]ˣ) : valuation K ((u : 𝒪[K]) : K) = 1 :=
  (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp u.isUnit
theorem normalizedValuation_unit (u : 𝒪[K]ˣ) : normalizedValuation K ((u : 𝒪[K]) : K) = 1 := by
  rw [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]
  exact valuation_unit u
theorem valuation_lt_one_of_mem_maximalIdeal {x : 𝒪[K]} (hx : x ∈ 𝓂[K]) :
    valuation K (x : K) < 1 := by
  refine lt_of_le_of_ne x.2 fun h ↦ ?_
  exact (IsLocalRing.mem_maximalIdeal x).mp hx
    ((Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mpr h)
theorem normalizedValuation_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    normalizedValuation K ϖ = WithZero.exp (-1) := by
  have hne : normalizedValuation K ϖ ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast hϖ.ne_zero
  have hlt : normalizedValuation K ϖ < 1 := by
    rw [← map_one (normalizedValuation K), normalizedValuation_lt_iff, map_one]
    exact valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
  obtain ⟨y, hy⟩ : ∃ y : K, normalizedValuation K y = WithZero.exp (-1) := by
    obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective
      ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm (WithZero.exp (-1)))
    exact ⟨y, by rw [normalizedValuation_apply, hy]; simp⟩
  have hexp : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hy1 : valuation K y < 1 := by
    rw [← map_one (valuation K), ← normalizedValuation_lt_iff, map_one, hy]; exact hexp
  have hymem : (⟨y, hy1.le⟩ : 𝒪[K]) ∈ 𝓂[K] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
    exact hy1.ne
  have hyϖ : valuation K y ≤ valuation K ϖ := by
    have := hϖ.maximalIdeal_eq_setOfPred_le_v_coe (v := valuation K)
    have h2 : (⟨y, hy1.le⟩ : 𝒪[K]) ∈ (𝓂[K] : Set 𝒪[K]) := hymem
    rw [this] at h2
    exact h2
  rw [← normalizedValuation_le_iff, hy] at hyϖ
  rw [← WithZero.exp_log hne] at hyϖ hlt ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hyϖ
  congr 1
  omega
noncomputable def ord (x : K) : ℤ := -WithZero.log (normalizedValuation K x)
end Valuation
section UnitsDecomposition
noncomputable def unitsIncl : 𝒪[K]ˣ →* Kˣ :=
  Units.map (𝒪[K].subtype : 𝒪[K] →+* K).toMonoidHom
variable {K}
@[simp]
theorem coe_unitsIncl (u : 𝒪[K]ˣ) : ((unitsIncl K u : Kˣ) : K) = ((u : 𝒪[K]) : K) := rfl
theorem unitsIncl_injective : Function.Injective (unitsIncl K) := by
  intro u w h
  ext
  have := congrArg Units.val h
  simpa using this
noncomputable def uniformizerUnit {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) : Kˣ :=
  Units.mk0 (ϖ : K) (by exact_mod_cast hϖ.ne_zero)
@[simp]
theorem coe_uniformizerUnit {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ((uniformizerUnit hϖ : Kˣ) : K) = ϖ := rfl
noncomputable def unitsOfIntProd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Multiplicative ℤ × 𝒪[K]ˣ →* Kˣ :=
  (zpowersHom Kˣ (uniformizerUnit hϖ)).coprod (unitsIncl K)
theorem coe_unitsOfIntProd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (n : Multiplicative ℤ)
    (u : 𝒪[K]ˣ) :
    ((unitsOfIntProd hϖ (n, u) : Kˣ) : K) = (ϖ : K) ^ n.toAdd * ((u : 𝒪[K]) : K) := by
  simp [unitsOfIntProd, zpowersHom_apply, Units.val_zpow_eq_zpow_val]
theorem normalizedValuation_unitsOfIntProd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    (n : Multiplicative ℤ) (u : 𝒪[K]ˣ) :
    normalizedValuation K (unitsOfIntProd hϖ (n, u) : K) = WithZero.exp (-n.toAdd) := by
  rw [coe_unitsOfIntProd, map_mul, map_zpow₀, normalizedValuation_uniformizer hϖ,
    normalizedValuation_unit, mul_one, ← WithZero.exp_zsmul]
  congr 1
  simp
theorem unitsOfIntProd_bijective {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Function.Bijective (unitsOfIntProd hϖ) := by
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨n, u⟩ h
    have hv := normalizedValuation_unitsOfIntProd hϖ n u
    rw [h, Units.val_one, map_one, ← WithZero.exp_zero, WithZero.exp_inj] at hv
    have hn : n = 1 := by
      rw [← toAdd_eq_zero]; omega
    subst hn
    have hu : unitsIncl K u = 1 := by
      simpa [unitsOfIntProd] using h
    rw [← map_one (unitsIncl K)] at hu
    rw [unitsIncl_injective hu]
    rfl
  · intro x
    obtain ⟨n, u, hx⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (K := K) hϖ x.ne_zero
    refine ⟨(Multiplicative.ofAdd n, u), ?_⟩
    ext
    rw [coe_unitsOfIntProd, hx, Units.smul_def, Algebra.smul_def, toAdd_ofAdd, mul_comm]
    rfl
noncomputable def unitsEquivIntProd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Kˣ ≃* Multiplicative ℤ × 𝒪[K]ˣ :=
  (MulEquiv.ofBijective (unitsOfIntProd hϖ) (unitsOfIntProd_bijective hϖ)).symm
end UnitsDecomposition
section Residue
noncomputable def unitsToResidue : 𝒪[K]ˣ →* 𝓀[K]ˣ :=
  Units.map (residue 𝒪[K]).toMonoidHom
theorem unitsToResidue_surjective : Function.Surjective (unitsToResidue K) :=
  surjective_units_map_of_local_ringHom _ residue_surjective inferInstance
@[simp]
theorem coe_unitsToResidue (u : 𝒪[K]ˣ) :
    ((unitsToResidue K u : 𝓀[K]ˣ) : 𝓀[K]) = residue 𝒪[K] u := rfl
theorem ker_unitsToResidue : (unitsToResidue K).ker = unitFiltration K 1 := by
  ext u
  rw [MonoidHom.mem_ker, mem_unitFiltration, pow_one, ← residue_eq_zero_iff, map_sub, map_one,
    sub_eq_zero, Units.ext_iff]
  rfl
noncomputable def unitsModPrincipalEquiv : 𝒪[K]ˣ ⧸ unitFiltration K 1 ≃* 𝓀[K]ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_unitsToResidue K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (unitsToResidue_surjective K))
@[simp]
theorem unitsModPrincipalEquiv_mk (u : 𝒪[K]ˣ) :
    unitsModPrincipalEquiv K (QuotientGroup.mk u) = unitsToResidue K u := rfl
end Residue
section Graded
variable {K} {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
include hϖ
theorem exists_sub_one_eq_mul {n : ℕ} (u : unitFiltration K n) :
    ∃ a : 𝒪[K], ((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ϖ ^ n * a :=
  (mem_maximalIdeal_pow_iff hϖ).mp u.2
noncomputable def filtrationCoeff {n : ℕ} (u : unitFiltration K n) : 𝒪[K] :=
  (exists_sub_one_eq_mul hϖ u).choose
theorem sub_one_eq_filtrationCoeff {n : ℕ} (u : unitFiltration K n) :
    ((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ϖ ^ n * filtrationCoeff hϖ u :=
  (exists_sub_one_eq_mul hϖ u).choose_spec
theorem filtrationCoeff_eq {n : ℕ} {u : unitFiltration K n} {a : 𝒪[K]}
    (h : ((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ϖ ^ n * a) : filtrationCoeff hϖ u = a :=
  mul_left_cancel₀ (pow_ne_zero n hϖ.ne_zero) ((sub_one_eq_filtrationCoeff hϖ u).symm.trans h)
theorem isUnit_one_add_mul {n : ℕ} (hn : 1 ≤ n) (a : 𝒪[K]) : IsUnit (1 + ϖ ^ n * a) := by
  have hm : ϖ ^ n * a ∈ 𝓂[K] :=
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (uniformizer_mem_maximalIdeal hϖ) n (by omega))
  simpa using isUnit_one_sub_self_of_mem_nonunits (-(ϖ ^ n * a))
    ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem hm))
noncomputable def filtrationGradedHom {n : ℕ} (hn : 1 ≤ n) :
    unitFiltration K n →* Multiplicative 𝓀[K] where
  toFun u := Multiplicative.ofAdd (residue 𝒪[K] (filtrationCoeff hϖ u))
  map_one' := by
    rw [filtrationCoeff_eq hϖ (a := 0) (by simp)]
    simp
  map_mul' u w := by
    have hu := sub_one_eq_filtrationCoeff hϖ u
    have hw := sub_one_eq_filtrationCoeff hϖ w
    have h := filtrationCoeff_eq hϖ (u := u * w)
      (a := filtrationCoeff hϖ u + filtrationCoeff hϖ w +
        ϖ ^ n * (filtrationCoeff hϖ u * filtrationCoeff hϖ w)) (by
      simp only [Subgroup.coe_mul, Units.val_mul]
      linear_combination ((w : 𝒪[K]ˣ) : 𝒪[K]) * hu + (1 + ϖ ^ n * filtrationCoeff hϖ u) * hw)
    rw [h, ← ofAdd_add]
    congr 1
    simp [residue_uniformizer hϖ, zero_pow (by omega : n ≠ 0)]
theorem filtrationGradedHom_apply {n : ℕ} (hn : 1 ≤ n) (u : unitFiltration K n) :
    filtrationGradedHom hϖ hn u = Multiplicative.ofAdd (residue 𝒪[K] (filtrationCoeff hϖ u)) :=
  rfl
theorem ker_filtrationGradedHom {n : ℕ} (hn : 1 ≤ n) :
    (filtrationGradedHom hϖ hn).ker =
      (unitFiltration K (n + 1)).subgroupOf (unitFiltration K n) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ,
    sub_one_eq_filtrationCoeff hϖ u, pow_succ,
    mul_dvd_mul_iff_left (pow_ne_zero n hϖ.ne_zero), ← mem_maximalIdeal_iff_dvd hϖ,
    ← residue_eq_zero_iff, filtrationGradedHom_apply]
  exact ofAdd_eq_one
theorem filtrationGradedHom_surjective {n : ℕ} (hn : 1 ≤ n) :
    Function.Surjective (filtrationGradedHom hϖ hn) := by
  intro r
  obtain ⟨a, ha⟩ := residue_surjective (Multiplicative.toAdd r)
  have hu := isUnit_one_add_mul hϖ hn a
  refine ⟨⟨hu.unit, ?_⟩, ?_⟩
  · rw [mem_unitFiltration, IsUnit.unit_spec, add_sub_cancel_left, mem_maximalIdeal_pow_iff hϖ]
    exact dvd_mul_right _ _
  · rw [filtrationGradedHom_apply, filtrationCoeff_eq hϖ (a := a) (by simp), ha]
    rfl
noncomputable def unitFiltrationGradedEquiv {n : ℕ} (hn : 1 ≤ n) :
    unitFiltration K n ⧸ (unitFiltration K (n + 1)).subgroupOf (unitFiltration K n) ≃*
      Multiplicative 𝓀[K] :=
  (QuotientGroup.quotientMulEquivOfEq (ker_filtrationGradedHom hϖ hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (filtrationGradedHom_surjective hϖ hn))
omit hϖ in
theorem relIndex_unitFiltration_succ {n : ℕ} (hn : 1 ≤ n) (hϖ : Irreducible ϖ) :
    (unitFiltration K (n + 1)).relIndex (unitFiltration K n) = Nat.card 𝓀[K] :=
  (Nat.card_congr (unitFiltrationGradedEquiv hϖ hn).toEquiv).trans rfl
end Graded
section Index
theorem index_unitFiltration_one : (unitFiltration K 1).index = Nat.card 𝓀[K] - 1 :=
  (Nat.card_congr (unitsModPrincipalEquiv K).toEquiv).trans (Nat.card_units 𝓀[K])
theorem index_unitFiltration {n : ℕ} (hn : 1 ≤ n) :
    (unitFiltration K n).index = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (n - 1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  induction n, hn using Nat.le_induction with
  | base => simp [index_unitFiltration_one]
  | succ n hn ih =>
    rw [← Subgroup.relIndex_mul_index (unitFiltration_succ_le K n),
      relIndex_unitFiltration_succ hn hϖ, ih, Nat.add_sub_cancel]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
theorem index_unitFiltration_ne_zero (n : ℕ) : (unitFiltration K n).index ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [index_unitFiltration K hn]
    have : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
    exact Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
instance (n : ℕ) : (unitFiltration K n).FiniteIndex := ⟨index_unitFiltration_ne_zero K n⟩
instance (n : ℕ) : Finite (𝒪[K]ˣ ⧸ unitFiltration K n) :=
  Subgroup.finite_quotient_of_finiteIndex
end Index
end GroundTheory.LocalField


