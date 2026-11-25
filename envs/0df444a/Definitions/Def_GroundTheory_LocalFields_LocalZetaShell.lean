-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
-- name    : GroundTheory_LocalFields_LocalZetaShell
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:33:27.904223+00:00
-- url     : https://prove2.me/theorems/148f923f-b5c6-58db-984e-34608c82ce04
-- title:
--   Local Zeta Shell
-- statement:
--   Definitions and structural lemmas for Local Zeta Shell, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaShell.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_mem_unitFiltrationUnits_zero_iff
import Theorems.Thm_GroundTheory_LocalField_mem_valBall_one_iff
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_multHaar_unitFiltrationUnits_zero
import Theorems.Thm_GroundTheory_LocalField_ord_mul
import Theorems.Thm_GroundTheory_LocalField_ord_uniformizer
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section Order
variable (K) in
theorem exists_units_ord_eq_one : ∃ π : Kˣ, ord (π : K) = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  exact ⟨Units.mk0 _ h0, by rw [Units.val_mk0]; exact ord_uniformizer hϖ⟩
variable (K) in

def unifUnit : Kˣ := (exists_units_ord_eq_one K).choose
theorem ord_unifUnit : ord (unifUnit K : K) = 1 := (exists_units_ord_eq_one K).choose_spec
theorem ord_units_mul (u v : Kˣ) : ord ((u * v : Kˣ) : K) = ord (u : K) + ord (v : K) := by
  rw [Units.val_mul, ord_mul u.ne_zero v.ne_zero]
theorem ord_units_zpow (u : Kˣ) (k : ℤ) : ord ((u ^ k : Kˣ) : K) = k * ord (u : K) := by
  rw [Units.val_zpow_eq_zpow_val]
  simp [ord, map_zpow₀, WithZero.log_zpow]
theorem ord_unifUnit_zpow (k : ℤ) : ord ((unifUnit K ^ k : Kˣ) : K) = k := by
  rw [ord_units_zpow, ord_unifUnit, mul_one]
theorem valuation_eq_one_iff_ord_eq_zero {x : K} (hx : x ≠ 0) :
    valuation K x = 1 ↔ ord x = 0 := by
  have h0 := mem_valBall_iff_le_ord (n := 0) hx
  have h1 := mem_valBall_iff_le_ord (n := 1) hx
  rw [mem_valBall_zero_iff, Valuation.mem_integer_iff] at h0
  rw [mem_valBall_one_iff] at h1
  constructor
  · intro h
    have a := h0.mp h.le
    have b : ¬ 1 ≤ ord x := fun hb => (h1.mpr hb).ne h
    omega
  · intro h
    refine le_antisymm (h0.mpr h.ge) (not_lt.mp fun hl => ?_)
    have := h1.mp hl
    omega
theorem mem_unitFiltrationUnits_zero_iff_ord {u : Kˣ} :
    u ∈ unitFiltrationUnits K 0 ↔ ord (u : K) = 0 := by
  rw [mem_unitFiltrationUnits_zero_iff, valuation_eq_one_iff_ord_eq_zero u.ne_zero]
end Order
section Shell
variable (K) in

def ordShell (k : ℤ) : Set Kˣ := {u | ord (u : K) = k}
theorem mem_ordShell {k : ℤ} {u : Kˣ} : u ∈ ordShell K k ↔ ord (u : K) = k := Iff.rfl
theorem ordShell_zero : ordShell K 0 = (unitFiltrationUnits K 0 : Set Kˣ) := by
  ext u
  rw [SetLike.mem_coe, mem_unitFiltrationUnits_zero_iff_ord]
  rfl
theorem mul_mem_ordShell_iff (v : Kˣ) {k : ℤ} {u : Kˣ} :
    v * u ∈ ordShell K (ord (v : K) + k) ↔ u ∈ ordShell K k := by
  simp only [mem_ordShell, ord_units_mul]
  omega
theorem iUnion_ordShell : ⋃ k, ordShell K k = Set.univ :=
  Set.eq_univ_of_forall fun _ => Set.mem_iUnion.mpr ⟨_, rfl⟩
end Shell
section Measure
variable [MeasurableSpace K] [BorelSpace K]
theorem measurable_units_val : Measurable (Units.val : Kˣ → K) :=
  measurableEmbedding_units_val.measurable
instance instMeasurableMul₂UnitsLocalField : MeasurableMul₂ Kˣ where
  measurable_mul := by
    rw [← measurableEmbedding_units_val.measurable_comp_iff]
    have : (Units.val ∘ fun p : Kˣ × Kˣ => p.1 * p.2) = fun p => (p.1 : K) * (p.2 : K) := by
      funext p
      simp
    rw [this]
    exact (measurable_units_val.comp measurable_fst).mul (measurable_units_val.comp measurable_snd)
instance instBorelSpaceUnitsLocalField : BorelSpace Kˣ := by
  refine ⟨?_⟩
  calc (Units.instMeasurableSpace : MeasurableSpace Kˣ) = MeasurableSpace.comap Units.val (borel K) := by
        rw [← BorelSpace.measurable_eq]
        rfl
    _ = borel Kˣ := by
        rw [(Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced, borel_comap]
theorem multHaar_ordShell (k : ℤ) : multHaar K (ordShell K k) = 1 := by
  have h : (fun u => unifUnit K ^ k * u) ⁻¹' ordShell K k = ordShell K 0 := by
    ext u
    have := mul_mem_ordShell_iff (K := K) (unifUnit K ^ k) (k := 0) (u := u)
    rwa [ord_unifUnit_zpow, add_zero] at this
  rw [← measure_preimage_mul (multHaar K) (unifUnit K ^ k), h, ordShell_zero,
    multHaar_unitFiltrationUnits_zero]
instance instSigmaFiniteMultHaar : SigmaFinite (multHaar K) := by
  refine Measure.sigmaFinite_of_countable (S := Set.range (ordShell K)) (Set.countable_range _) ?_ ?_
  · rintro _ ⟨k, rfl⟩
    rw [multHaar_ordShell]
    exact ENNReal.one_lt_top
  · rw [Set.sUnion_range, iUnion_ordShell]
end Measure
section Power
end Power
end GroundTheory.LocalField


