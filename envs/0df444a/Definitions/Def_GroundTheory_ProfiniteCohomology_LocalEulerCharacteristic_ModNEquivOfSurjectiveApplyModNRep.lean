-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
-- name    : GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:27.223632+00:00
-- url     : https://prove2.me/theorems/ccc1fd29-5ec4-41c1-8e63-ddb09bdbe79f
-- title:
--   Mod NEquiv Of Surjective Apply Mod NRep
-- statement:
--   Definitions and structural lemmas for Mod NEquiv Of Surjective Apply Mod NRep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_coeff_injective
import Theorems.Thm_GroundTheory_LocalField_ord_mul
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
section MonoidAlgebra
instance finite_monoidAlgebra {R M : Type*} [Semiring R] [Finite R] [Finite M] :
    Finite (MonoidAlgebra R M) :=
  Finite.of_injective (fun x : MonoidAlgebra R M ↦ (x.coeff : M → R))
    (fun _ _ h ↦ MonoidAlgebra.coeff_injective (DFunLike.coe_injective h))
end MonoidAlgebra
section ModNEquiv
variable {n : ℕ} {A X : Type*} [AddCommGroup A] [AddCommGroup X] [Module (ZMod n) X]
noncomputable def modNEquivOfSurjective (φ : A →+ X) (hs : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ A n)) :
    ModN A n ≃ₗ[ZMod n] X :=
  LinearEquiv.ofBijective
    (((LinearMap.range (LinearMap.lsmul ℤ A n)).liftQ φ.toIntLinearMap
      fun a ha ↦ LinearMap.mem_ker.mpr ((hker a).mpr ha)).toAddMonoidHom.toZModLinearMap n)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact (Submodule.Quotient.mk_eq_zero _).mpr ((hker a).mp hx),
    fun x ↦ by
      obtain ⟨a, ha⟩ := hs x
      exact ⟨Submodule.Quotient.mk a, ha⟩⟩
end ModNEquiv
section Int
abbrev trivialIntAction (Γ : Type*) [Monoid Γ] : DistribMulAction Γ (ULift.{u} ℤ) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
end Int
section Valuation
variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
noncomputable def ordHom : Additive Fˣ →+ ULift.{u} ℤ where
  toFun x := ULift.up (ord ((x.toMul : Fˣ) : F))
  map_zero' := by
    apply ULift.ext
    simp [ord]
  map_add' x y := by
    apply ULift.ext
    simp [ord_mul x.toMul.ne_zero y.toMul.ne_zero]
variable {F}
end Valuation
section Subgroup
end Subgroup
section Torsion
variable {F : Type*} [Field F] [ValuativeRel F]
end Torsion
section Residue
variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  {p : ℕ}
noncomputable def modNIntegerEquiv : ModN 𝒪[E] p ≃ₗ[ℤ] 𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])} :=
  (Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [mem_range_lsmul_iff, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    simp only [nsmul_eq_mul, mul_comm])).trans
    (Submodule.Quotient.restrictScalarsEquiv ℤ (Ideal.span {(p : 𝒪[E])}))
variable [Fact p.Prime]
end Residue
section Filtration
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {p e : ℕ} {ε : 𝒪[F]ˣ} (hpe : (p : 𝒪[F]) = ϖ ^ e * ε)
include hϖ hpe
end Filtration
section Galois
variable {E F : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]
variable {l : ℕ} [NeZero l] (d : AdditiveFunction.{u} l (F ≃ₐ[E] F))
attribute [local instance] integerAction unitFiltrationAction
attribute [local instance] maxPowAction normalSubAction
end Galois
section LemmaA
variable {E F : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F] [IsGalois E F]
  {l : ℕ} [Fact l.Prime] (d : AdditiveFunction.{u} l (F ≃ₐ[E] F))
attribute [local instance] integerAction unitFiltrationAction maxPowAction normalSubAction
end LemmaA
end GroundTheory.ProfCoh


