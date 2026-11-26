-- Prove2me | Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
-- name    : FourierJacobi_Measure_MultiplicativeHaar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:52:25.718134+00:00
-- url     : https://prove2.me/theorems/b0f1580b-0247-4a84-8768-ae078870fce2
-- title:
--   Multiplicative Haar
-- statement:
--   Definitions and structural lemmas for Multiplicative Haar, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/MultiplicativeHaar.lean

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.Topology.Algebra.Group.Units
import Theorems.Thm_FourierJacobi_Measure_canonicalValuation_uniformizer_smul
import Theorems.Thm_FourierJacobi_Measure_existsUnique_integerShell
import Theorems.Thm_FourierJacobi_Measure_exists_integerShell_iff_ne_zero
import Theorems.Thm_FourierJacobi_Measure_exists_integral_canonical_uniformizer
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_nonnegative_iff
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero


set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal Pointwise
namespace FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
local instance multiplicativeHaar_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance
def valuationRingUnits : Subgroup Kˣ := (𝒪[K]).toSubmonoid.units
theorem valuationRingUnits_isCompact : IsCompact (valuationRingUnits K : Set Kˣ) :=
  Submonoid.units_isCompact (S := (𝒪[K]).toSubmonoid)
    (IsNonarchimedeanLocalField.isCompact_closedBall K 1)
theorem valuationRingUnits_isOpen : IsOpen (valuationRingUnits K : Set Kˣ) :=
  Submonoid.isOpen_units (U := (𝒪[K]).toSubmonoid) (valuation K).isOpen_integer
def valuationRingUnitsCompact : TopologicalSpace.PositiveCompacts Kˣ :=
  ⟨⟨valuationRingUnits K, valuationRingUnits_isCompact K⟩, by
    rw [(valuationRingUnits_isOpen K).interior_eq]
    exact ⟨1, (valuationRingUnits K).one_mem⟩⟩
def unitValuationShell (n : ℤ) : Set Kˣ :=
  {u | localFieldValuation K (u : K) = (n : WithTop ℤ)}
theorem unitValuationShell_zero_eq :
    unitValuationShell K 0 = (valuationRingUnits K : Set Kˣ) := by
  ext u
  obtain ⟨m, hm⟩ := (exists_integerShell_iff_ne_zero K (u : K)).mpr u.ne_zero
  obtain ⟨n, hn⟩ := (exists_integerShell_iff_ne_zero K (↑(u⁻¹) : K)).mpr (u⁻¹).ne_zero
  have hadd : (m : WithTop ℤ) + (n : WithTop ℤ) = 0 := by
    rw [← hm, ← hn, ← (localFieldValuation K).map_mul]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, (localFieldValuation K).map_one]
  have hmn : m + n = 0 := by exact_mod_cast hadd
  change localFieldValuation K (u : K) = (0 : WithTop ℤ) ↔
    (u : K) ∈ 𝒪[K] ∧ (↑(u⁻¹) : K) ∈ 𝒪[K]
  rw [← localFieldValuation_nonnegative_iff, ← localFieldValuation_nonnegative_iff, hm, hn]
  change (m : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) ↔
    ((0 : ℤ) : WithTop ℤ) ≤ (m : WithTop ℤ) ∧
    ((0 : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ)
  simp only [WithTop.coe_inj, WithTop.coe_le_coe]
  omega
theorem unitValuationShell_eq_uniformizer_smul (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) (n : ℤ) :
    unitValuationShell K n =
      (canonicalUniformizerUnit K π hπ ^ n) • (valuationRingUnits K : Set Kˣ) := by
  ext u
  rw [Set.mem_smul_set_iff_inv_smul_mem, ← unitValuationShell_zero_eq, ← zpow_neg]
  change localFieldValuation K (u : K) = (n : WithTop ℤ) ↔
    localFieldValuation K ((canonicalUniformizerUnit K π hπ ^ (-n)) • (u : K)) = 0
  rw [canonicalValuation_uniformizer_smul]
  generalize localFieldValuation K (u : K) = v
  induction v using WithTop.recTopCoe with
  | top => simp
  | coe m =>
    rw [← WithTop.coe_add]
    change (m : WithTop ℤ) = (n : WithTop ℤ) ↔
      ((-n + m : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ)
    simp only [WithTop.coe_inj]
    omega
theorem existsUnique_unitValuationShell (u : Kˣ) :
    ∃! n : ℤ, u ∈ unitValuationShell K n :=
  existsUnique_integerShell K (u : K) u.ne_zero
theorem iUnion_unitValuationShell_eq : (⋃ n : ℤ, unitValuationShell K n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro u
  exact Set.mem_iUnion.mpr (existsUnique_unitValuationShell K u).exists
variable [MeasurableSpace Kˣ] [BorelSpace Kˣ]
def multiplicativeHaar : MeasureTheory.Measure Kˣ :=
  MeasureTheory.Measure.haarMeasure (valuationRingUnitsCompact K)
instance multiplicativeHaar_isHaarMeasure : (multiplicativeHaar K).IsHaarMeasure := by
  unfold multiplicativeHaar
  infer_instance
theorem multiplicativeHaar_valuationRingUnits :
    multiplicativeHaar K (valuationRingUnits K : Set Kˣ) = 1 :=
  MeasureTheory.Measure.haarMeasure_self
theorem multiplicativeHaar_unitValuationShell (n : ℤ) :
    multiplicativeHaar K (unitValuationShell K n) = 1 := by
  obtain ⟨π, hπ⟩ := exists_integral_canonical_uniformizer K
  rw [unitValuationShell_eq_uniformizer_smul K π hπ n, measure_smul,
    multiplicativeHaar_valuationRingUnits]
instance multiplicativeHaar_sigmaFinite : SigmaFinite (multiplicativeHaar K) := by
  apply Measure.sigmaFinite_of_countable (Set.countable_range (unitValuationShell K))
  · rintro s ⟨n, rfl⟩
    rw [multiplicativeHaar_unitValuationShell]
    exact ENNReal.one_lt_top
  · simpa only [Set.sUnion_range] using iUnion_unitValuationShell_eq K
end FourierJacobi.Measure


