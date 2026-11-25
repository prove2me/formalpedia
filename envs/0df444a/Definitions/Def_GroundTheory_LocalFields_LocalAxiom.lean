-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalAxiom
-- name    : GroundTheory_LocalFields_LocalAxiom
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T09:44:02.664861+00:00
-- url     : https://prove2.me/theorems/24447318-2aa6-5f71-9aaf-3025ddbfd724
-- title:
--   Local Axiom
-- statement:
--   Definitions and structural lemmas for Local Axiom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiom.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_GroundTheory_LocalField_Abstract_TateModel_natCard_tateNegOne
import Theorems.Thm_GroundTheory_LocalField_Abstract_TateModel_natCard_tateZero
import Theorems.Thm_GroundTheory_LocalField_Abstract_TateModel_relIndex_eq_natCard
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_baseUnitsEquiv_norm
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_finiteDimensional_extendScalars
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_inertiaDegree_unramifiedDegree_fixingSubgroup
import Theorems.Thm_GroundTheory_LocalField_isDiscreteModule_units
import Theorems.Thm_GroundTheory_LocalField_maximalUnramifiedExtensionGaloisEquiv_apply
import Theorems.Thm_GroundTheory_LocalField_natCard_tateNegOne_units
import Theorems.Thm_GroundTheory_LocalField_natCard_tateZero_units
import Theorems.Thm_GroundTheory_LocalField_normal_extendScalars
import Theorems.Thm_GroundTheory_LocalField_ord_mul
import Theorems.Thm_GroundTheory_LocalField_ord_norm
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_unramifiedDegree_spec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply
attribute [local simp] GroundTheory.LocalField.maximalUnramifiedExtensionGaloisEquiv_apply
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
namespace GroundTheory.LocalField
open Abstract ValuativeRel
section Valuation
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
noncomputable def ordUnitsHom : Kˣ →* Multiplicative ℤ̂ where
  toFun x := Multiplicative.ofAdd ((ord (x : K) : ℤ) : ℤ̂)
  map_one' := by
    rw [Units.val_one, ord_one, Int.cast_zero, ofAdd_zero]
  map_mul' x y := by
    rw [Units.val_mul, ord_mul x.ne_zero y.ne_zero, Int.cast_add, ofAdd_add]
@[simp]
theorem toAdd_ordUnitsHom (x : Kˣ) :
    (ordUnitsHom K x).toAdd = ((ord (x : K) : ℤ) : ℤ̂) :=
  rfl
variable {K} in

theorem exists_ordUnitsHom_eq (n : ℤ) :
    ∃ x : Kˣ, ordUnitsHom K x = Multiplicative.ofAdd (n : ℤ̂) := by
  obtain ⟨x, hx, h⟩ := exists_ord_eq K n
  refine ⟨Units.mk0 x hx, Multiplicative.toAdd.injective ?_⟩
  rw [toAdd_ordUnitsHom, Units.val_mk0, h, toAdd_ofAdd]
end Valuation
section Data
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
noncomputable def localValuation : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Multiplicative ℤ̂ :=
  (ordUnitsHom K).comp baseUnitsEquiv.toMonoidHom
theorem localValuation_apply (a : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))) :
    localValuation K Ω a = ordUnitsHom K (baseUnitsEquiv a) :=
  rfl
variable {K Ω}
theorem range_localValuation_comp_norm_of_eq (H : Subgroup (Ω ≃ₐ[K] Ω))
    [(H.subgroupOf ⊤).FiniteIndex] (L : IntermediateField K Ω) [FiniteDimensional K L]
    (hL : L.fixingSubgroup = H) :
    ((localValuation K Ω).comp (norm Ωˣ ⊤ H)).range =
      (localValuation K Ω).range.map (powMonoidHom (inertiaDegree (unramifiedDegree K Ω) H)) := by
  subst hL
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have hsc : IsSepClosed Ω := IsSepClosure.sep_closed K
  rw [inertiaDegree_unramifiedDegree_fixingSubgroup]
  have key : ∀ u : Lˣ, ordUnitsHom K (normUnits K L u) =
      Multiplicative.ofAdd (((residueDegree K L : ℤ) * ord (u : L) : ℤ) : ℤ̂) := fun u => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ordUnitsHom, coe_normUnits, ord_norm, toAdd_ofAdd]
  ext z
  simp only [MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply, powMonoidHom_apply]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := exists_ordUnitsHom_eq (K := K) (ord ((fixedModuleUnitsEquiv L a : Lˣ) : L))
    refine ⟨_, ⟨baseUnitsEquiv.symm x, rfl⟩, ?_⟩
    rw [localValuation_apply, localValuation_apply, MulEquiv.apply_symm_apply, hx,
      baseUnitsEquiv_norm, key]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, Int.cast_mul,
      Int.cast_natCast, nsmul_eq_mul]
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    obtain ⟨y, hy, hy'⟩ := exists_ord_eq L (ord ((baseUnitsEquiv b : Kˣ) : K))
    refine ⟨(fixedModuleUnitsEquiv L).symm (Units.mk0 y hy), ?_⟩
    rw [localValuation_apply, localValuation_apply, baseUnitsEquiv_norm, MulEquiv.apply_symm_apply,
      key, Units.val_mk0, hy']
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ordUnitsHom, toAdd_ofAdd, Int.cast_mul,
      Int.cast_natCast, nsmul_eq_mul]
theorem intCast_mem_range_localValuation (n : ℤ) :
    Multiplicative.ofAdd (n : ℤ̂) ∈ (localValuation K Ω).range := by
  obtain ⟨x, hx⟩ := exists_ordUnitsHom_eq (K := K) n
  exact ⟨baseUnitsEquiv.symm x, by rw [localValuation_apply, MulEquiv.apply_symm_apply, hx]⟩
variable (K Ω)
noncomputable def localClassFieldData : ClassFieldData (Ω ≃ₐ[K] Ω) Ωˣ where
  deg := unramifiedDegree K Ω
  continuous_deg := unramifiedDegree_spec.1
  surjective_deg := unramifiedDegree_spec.2.1
  val := localValuation K Ω
  intCast_mem_range_val := intCast_mem_range_localValuation
  exists_eq_intCast_add_nsmul n _ a := by
    refine ⟨ord ((baseUnitsEquiv a : Kˣ) : K), 1, ?_⟩
    rw [map_one, toAdd_one, smul_zero, add_zero]
    rfl
  range_val_comp_norm U :=
    range_localValuation_comp_norm_of_eq (U : Subgroup (Ω ≃ₐ[K] Ω))
      (IntermediateField.fixedField (U : Subgroup (Ω ≃ₐ[K] Ω)))
      (fixingSubgroup_fixedField_openSubgroup U)
end Data
section Axiom
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
theorem natCard_tate_of_isCyclic (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) [(L'.subgroupOf K').Normal]
    [(L'.subgroupOf K').FiniteIndex] (E F : IntermediateField K Ω) [FiniteDimensional K E]
    [FiniteDimensional K F] (hEF : E ≤ F) (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')
    (hcyc : IsCyclic (K' ⧸ L'.subgroupOf K')) :
    Nat.card (tateZero Ωˣ K' L') = L'.relIndex K' ∧ Nat.card (tateNegOne Ωˣ K' L') = 1 := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := K) E
  have := normal_extendScalars K' L' hEF hK hL
  have := finiteDimensional_extendScalars hEF
  have : IsGalois E (IntermediateField.extendScalars hEF) :=
    isGalois_iff.2 ⟨inferInstance, inferInstance⟩
  let T := galoisTateModel K' L' hEF hK hL
  have : IsCyclic (IntermediateField.extendScalars hEF ≃ₐ[E] IntermediateField.extendScalars hEF) :=
    isCyclic_of_surjective T.quotientEquiv.toMonoidHom T.quotientEquiv.surjective
  refine ⟨?_, ?_⟩
  · rw [T.natCard_tateZero, natCard_tateZero_units, T.relIndex_eq_natCard,
      IsGalois.card_aut_eq_finrank]
  · rw [T.natCard_tateNegOne, natCard_tateNegOne_units]
variable (K Ω) in

theorem classFieldAxiom_units : ClassFieldAxiom (Ω ≃ₐ[K] Ω) Ωˣ := by
  intro U V hVU _ hcyc
  exact natCard_tate_of_isCyclic (U : Subgroup (Ω ≃ₐ[K] Ω)) (V : Subgroup (Ω ≃ₐ[K] Ω))
    (IntermediateField.fixedField (U : Subgroup (Ω ≃ₐ[K] Ω)))
    (IntermediateField.fixedField (V : Subgroup (Ω ≃ₐ[K] Ω)))
    (IntermediateField.fixedField_antitone hVU) (fixingSubgroup_fixedField_openSubgroup U)
    (fixingSubgroup_fixedField_openSubgroup V) hcyc
end Axiom
section Theory
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
noncomputable def localClassFieldTheory : ClassFieldTheory (Ω ≃ₐ[K] Ω) Ωˣ where
  toClassFieldData := localClassFieldData K Ω
  isDiscreteModule := isDiscreteModule_units
  classFieldAxiom := classFieldAxiom_units K Ω
end Theory
end GroundTheory.LocalField


