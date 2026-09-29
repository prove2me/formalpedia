-- Prove2me | solution 1 for AutomorphicForm.exists_idelesBaseChange_continuous_injective_norm_pow_range_eq_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/52d7ec61-d725-530c-8738-5e4c17aa0147

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_idelesBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_idelesBaseChange_continuous_injective_norm_pow_range_eq_fixed
p2m_attr_erase "instance" "instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.preimage_mulLeft_smul ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in
open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    ∃ θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ, Continuous θ ∧ Function.Injective θ ∧
      (∀ a, NumberField.TateGlobal.ideleNorm L (θ a) = NumberField.TateGlobal.ideleNorm K a ^ Module.finrank K L) ∧
      (∀ k : Kˣ, θ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) =
        Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (algebraMap K L : K →* L) k)) ∧
      (∀ b : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ b = b ↔ b ∈ Set.range θ)  := by
  classical
  obtain ⟨hinj, hfix, -, -⟩ :=
    M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm K L D
  refine ⟨AutomorphicForm.TransversalMeasure.idelesBaseChange K L, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact (M4aHerbrand.Bridge.continuous_genuineβ K L).units_map _
  ·
    intro a b hab
    apply Units.ext
    apply hinj
    have := congrArg Units.val hab
    simpa [AutomorphicForm.TransversalMeasure.idelesBaseChange, M4aHerbrand.GenuineDescent.genuineBaseChange_β] using this
  ·
    intro a
    exact NumberField.TateGlobal.ideleNorm_idelesBaseChange K L a
  ·
    intro k
    apply Units.ext
    simp only [AutomorphicForm.TransversalMeasure.idelesBaseChange, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe]
    have := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β_compat (k : K)
    rw [M4aHerbrand.GenuineDescent.genuineBaseChange_β] at this
    simpa using this
  ·
    intro b
    have hall : D.unitsAct σ b = b ↔ ∀ τ : L ≃ₐ[K] L, D.unitsAct τ b = b := by
      constructor
      · intro hb τ
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
        rw [map_zpow]
        induction n using Int.induction_on with
        | zero => simp
        | succ n ih => rw [zpow_add_one, MulAut.mul_apply, hb, ih]
        | pred n ih =>
          rw [zpow_sub_one, MulAut.mul_apply]
          have hb' : (D.unitsAct σ)⁻¹ b = b := by
            rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]; exact hb.symm
          rw [hb', ih]
      · intro h; exact h σ
    rw [hall, hfix b]
    simp only [MonoidHom.mem_range, Set.mem_range, AutomorphicForm.TransversalMeasure.idelesBaseChange,
      M4aHerbrand.GenuineDescent.genuineBaseChange_β]

end S_AutomorphicForm_exists_idelesBaseChange_continuous_injective_norm_pow_range_eq_fixed
end P2MW
export P2MW.S_AutomorphicForm_exists_idelesBaseChange_continuous_injective_norm_pow_range_eq_fixed (solution)
