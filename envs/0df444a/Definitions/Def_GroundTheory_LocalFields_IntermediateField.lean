-- Prove2me | Definitions.Def_GroundTheory_LocalFields_IntermediateField
-- name    : GroundTheory_LocalFields_IntermediateField
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:44:23.877441+00:00
-- url     : https://prove2.me/theorems/95b64cad-3479-4300-b75e-c1df560378b5
-- title:
--   Intermediate Field
-- statement:
--   Definitions and structural lemmas for Intermediate Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/IntermediateField.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_valuation_algEquiv_apply
import Theorems.Thm_GroundTheory_LocalField_valuativeExtension_algHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel Topology Filter
section Algebraic
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [ValuativeRel L]
  (E : IntermediateField K L)
instance intermediateField_valuativeRel : ValuativeRel E :=
  ValuativeRel.ofValuation ((valuation L).comap (algebraMap E L))
variable {E} in

@[simp]
theorem IntermediateField.coe_vle_coe_iff (x y : E) : (x : L) ≤ᵥ (y : L) ↔ x ≤ᵥ y :=
  by exact (valuation L).vle_iff_le
instance intermediateField_valuativeExtension_right : ValuativeExtension E L :=
  ⟨IntermediateField.coe_vle_coe_iff⟩
instance intermediateField_valuativeExtension_left [ValuativeRel K] [ValuativeExtension K L] :
    ValuativeExtension K E :=
  ⟨fun a b ↦ by
    rw [← IntermediateField.coe_vle_coe_iff, IntermediateField.coe_algebraMap_apply,
      IntermediateField.coe_algebraMap_apply, ValuativeExtension.vle_iff_vle]⟩
variable {E} in

theorem IntermediateField.valuation_coe (x : E) :
    valuation L (x : L) = ValuativeExtension.mapValueGroupWithZero E L (valuation E x) :=
  (ValuativeExtension.mapValueGroupWithZero_valuation (A := E) (B := L) x).symm
end Algebraic
section Topological
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (E : IntermediateField K L)
theorem IntermediateField.isClosed_of_isNonarchimedeanLocalField : IsClosed (E : Set L) := by
  let := nontriviallyNormedField K
  have := completeSpace_nontriviallyNormedField K
  have := t2Space_of_isNonarchimedeanLocalField L
  have : FiniteDimensional K (Subalgebra.toSubmodule E.toSubalgebra) :=
    (inferInstance : FiniteDimensional K E)
  exact (Subalgebra.toSubmodule E.toSubalgebra).closed_of_finiteDimensional
instance intermediateField_isNonarchimedeanLocalField : IsNonarchimedeanLocalField E := by

  have small : ∀ γ : (ValueGroupWithZero L)ˣ, ∃ b : E, b ≠ 0 ∧ valuation L (b : L) < γ := by
    intro γ
    obtain ⟨δ, hδ0, hδ1⟩ := IsNontrivial.exists_lt_one (R := K)
    obtain ⟨a, rfl⟩ := valuation_surjective δ
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hδ0
    have hb : valuation L (algebraMap K L a) < 1 :=
      (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) a).mpr hδ1
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hb γ
    refine ⟨algebraMap K E (a ^ n), by simp [ha0], ?_⟩
    rw [IntermediateField.coe_algebraMap_apply, map_pow, map_pow]
    exact hn
  have hmono := ValuativeExtension.mapValueGroupWithZero_strictMono (A := E) (B := L)
  have hval := IntermediateField.valuation_coe (E := E)
  have : ContinuousConstVAdd E E :=
    ⟨fun c ↦ continuous_induced_rng.2 (continuous_const.add continuous_subtype_val)⟩
  have hvt : IsValuativeTopology E := by
    refine IsValuativeTopology.of_zero fun s ↦ ?_
    have hb := (IsValuativeTopology.hasBasis_nhds_zero L).comap ((↑) : E → L)
    rw [IsInducing.subtypeVal.nhds_eq_comap, ZeroMemClass.coe_zero]
    refine hb.mem_iff.trans ?_
    constructor
    · rintro ⟨γ, -, hγ⟩
      obtain ⟨b, hb0, hb⟩ := small γ
      refine ⟨Units.mk0 (valuation E b) (by simpa using hb0), fun z hz ↦ hγ ?_⟩
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Units.val_mk0] at hz ⊢
      rw [hval] at hb ⊢
      exact (hmono hz).trans hb
    · rintro ⟨γ, hγ⟩
      have hγ0 : ValuativeExtension.mapValueGroupWithZero E L γ ≠ 0 := by
        rw [← map_zero (ValuativeExtension.mapValueGroupWithZero E L)]
        exact (hmono (zero_lt_iff.mpr γ.ne_zero)).ne'
      refine ⟨Units.mk0 _ hγ0, trivial, fun z hz ↦ hγ ?_⟩
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Units.val_mk0] at hz ⊢
      rw [hval] at hz
      exact hmono.lt_iff_lt.mp hz
  have hlc : LocallyCompactSpace E :=
    (IntermediateField.isClosed_of_isNonarchimedeanLocalField E).isClosedEmbedding_subtypeVal
      |>.locallyCompactSpace
  have hnt : IsNontrivial E := by
    obtain ⟨b, hb0, hb⟩ := small 1
    refine ⟨⟨valuation E b, by simpa using hb0, fun h ↦ ?_⟩⟩
    rw [hval, h, map_one] at hb
    exact hb.false
  exact { hvt, hlc, hnt with }
example : IsNonarchimedeanLocalField E := inferInstance
example : ValuativeExtension E L := inferInstance
example : Algebra 𝒪[E] 𝒪[L] := inferInstance
example : Algebra 𝓀[E] 𝓀[L] := inferInstance
example (σ : L ≃ₐ[E] L) (x : L) : valuation L (σ x) = valuation L x :=
  valuation_algEquiv_apply E L σ x
example (F : IntermediateField K L) (h : E ≤ F) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    ValuativeExtension E F :=
  valuativeExtension_algHom (K := K) (IntermediateField.inclusion h)
end Topological
end GroundTheory.LocalField


