-- Prove2me | Definitions.Def_GroundTheory_LocalFields_Examples
-- name    : GroundTheory_LocalFields_Examples
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:38.288577+00:00
-- url     : https://prove2.me/theorems/8c41171d-1c71-4f74-9fcf-73c80c97ae11
-- title:
--   Examples
-- statement:
--   Definitions and structural lemmas for Examples, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Examples.lean

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
open ValuativeRel WithZero
theorem isValuativeTopology_of_valued {R : Type*} [CommRing R] [ValuativeRel R]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀]
    [(Valued.v : Valuation R Γ₀).Compatible] : IsValuativeTopology R :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle (Valued.v : Valuation R Γ₀) fun {s} => by
    simpa using (Valued.hasBasis_nhds_zero R Γ₀).mem_iff (t := s)
namespace Padic
variable (p : ℕ) [hp : Fact p.Prime]
theorem mulValuation_le_iff_norm_le (x y : ℚ_[p]) :
    Padic.mulValuation x ≤ Padic.mulValuation y ↔ ‖x‖ ≤ ‖y‖ := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hx, hy]
  rw [Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_eq_zpow_neg_valuation hy,
    zpow_le_zpow_iff_right₀ (by exact_mod_cast hp.out.one_lt)]
  simp [hx, hy, -exp_neg]
instance isValuativeTopology : IsValuativeTopology ℚ_[p] :=
  letI : Valued ℚ_[p] NNReal := NormedField.toValued
  haveI : (Valued.v : Valuation ℚ_[p] NNReal).Compatible := ⟨fun x y => by
    rw [Valuation.Compatible.vle_iff_le (v := Padic.mulValuation) x y,
      mulValuation_le_iff_norm_le]
    rfl⟩
  isValuativeTopology_of_valued
instance isNonarchimedeanLocalField : IsNonarchimedeanLocalField ℚ_[p] where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance
end Padic
namespace LaurentSeries
open _root_.LaurentSeries HahnSeries
variable (K : Type*) [Field K]
noncomputable instance : ValuativeRel K⸨X⸩ := .ofValuation Valued.v
instance : (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).Compatible := .ofValuation _
instance : IsValuativeTopology K⸨X⸩ := isValuativeTopology_of_valued
theorem valued_X : Valued.v (single 1 1 : K⸨X⸩) = exp (-1 : ℤ) := by
  simpa using valuation_single_zpow (K := K) 1
instance : ValuativeRel.IsNontrivial K⸨X⸩ where
  condition := ⟨valuation _ (single 1 1), by simp, by
    intro h
    have := (ValuativeRel.isEquiv (valuation K⸨X⸩) Valued.v).eq_one_iff_eq_one.mp h
    rw [valued_X] at this
    simp at this⟩
section Finite
variable {K}
theorem mem_integer_iff (f : K⸨X⸩) :
    f ∈ Valued.integer K⸨X⸩ ↔ ∀ n : ℤ, n < 0 → f.coeff n = 0 := by
  change Valued.v f ≤ 1 ↔ _
  simpa using valuation_le_iff_coeff_lt_eq_zero (K := K) (D := 0) (f := f)
theorem C_mem_integer (c : K) : (HahnSeries.C c : K⸨X⸩) ∈ Valued.integer K⸨X⸩ := by
  rw [mem_integer_iff]
  intro n hn
  simp [HahnSeries.C_apply, hn.ne]
theorem residue_C_coeff_zero (x : Valued.integer K⸨X⸩) :
    IsLocalRing.residue _ ⟨HahnSeries.C ((x : K⸨X⸩).coeff 0), C_mem_integer _⟩ =
      IsLocalRing.residue _ x := by
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  have hx := (mem_integer_iff (x : K⸨X⸩)).mp x.2
  have : Valued.v (HahnSeries.C ((x : K⸨X⸩).coeff 0) - (x : K⸨X⸩)) ≤ exp (-1 : ℤ) := by
    rw [valuation_le_iff_coeff_lt_eq_zero]
    intro n hn
    rcases lt_or_eq_of_le (show n ≤ 0 by omega) with h | rfl
    · simp [HahnSeries.C_apply, h.ne, hx n h]
    · simp [HahnSeries.C_apply]
  refine lt_of_le_of_lt this ?_
  rw [← exp_zero, exp_lt_exp]
  norm_num
variable (K) [Finite K]
instance finite_residueField : Finite (IsLocalRing.ResidueField (Valued.integer K⸨X⸩)) :=
  Finite.of_surjective (fun c : K => IsLocalRing.residue _ ⟨HahnSeries.C c, C_mem_integer c⟩)
    fun r => by
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
      exact ⟨_, residue_C_coeff_zero x⟩
end Finite
instance : Nontrivial (MonoidWithZeroHom.valueGroup
    (MonoidWithZeroHom.ofClass (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰))) := by
  refine ⟨⟨⟨Units.mk0 (exp (-1 : ℤ)) (by simp), MonoidWithZeroHom.mem_valueGroup _ ?_⟩, 1, ?_⟩⟩
  · exact ⟨single 1 1, valued_X K⟩
  · intro h
    have := congrArg (fun u : MonoidWithZeroHom.valueGroup _ => ((u : ℤᵐ⁰ˣ) : ℤᵐ⁰)) h
    simp at this
instance : IsDiscreteValuationRing (Valued.integer K⸨X⸩) :=
  inferInstanceAs (IsDiscreteValuationRing (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring)
instance [Finite K] : LocallyCompactSpace K⸨X⸩ := by
  let := Valuation.IsRankOneDiscrete.rankOne (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰)
    (e := 2) one_lt_two
  have hc : CompactSpace (Valued.integer K⸨X⸩) :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
      ⟨(Valued.isClosed_integer K⸨X⸩).completeSpace_coe, inferInstance, inferInstance⟩
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup
    (isCompact_iff_compactSpace.mpr hc) ((Valued.isOpen_integer K⸨X⸩).mem_nhds (zero_mem _))
instance isNonarchimedeanLocalField [Finite K] : IsNonarchimedeanLocalField K⸨X⸩ where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance
end LaurentSeries
end GroundTheory.LocalField


