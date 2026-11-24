-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_UnitsInflationCochainsFHomApply
-- name    : GroundTheory_ProfiniteCohomology_GaloisCohomology_UnitsInflationCochainsFHomApply
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:40:00.564401+00:00
-- url     : https://prove2.me/theorems/69f318dd-3da1-4772-b28a-7f8954b6708d
-- title:
--   Units Inflation Cochains FHom Apply
-- statement:
--   Definitions and structural lemmas for Units Inflation Cochains FHom Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisCohomology/UnitsInflationCochainsFHomApply.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_locallyConstantCochains
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory groupCohomology
universe u
section ULiftInt
def uliftIntLinearMap {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    A →ₗ[ULift.{u} ℤ] B where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    change f (r.down • x) = r.down • f x
    exact map_zsmul f r.down x
@[simp]
theorem uliftIntLinearMap_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (x : A) : uliftIntLinearMap.{u} f x = f x :=
  rfl
end ULiftInt
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
section Kummer
variable (n : ℕ)
def rootsOfUnityToUnits : galRootsOfUnity.{u} K L n ⟶ galUnits.{u} K L :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (rootsOfUnity n L).subtype), fun σ => by
    ext x
    rfl⟩
@[simp]
theorem rootsOfUnityToUnits_hom_apply (x : Additive (rootsOfUnity n L)) :
    ((rootsOfUnityToUnits K L n).hom x : Additive Lˣ) =
      Additive.ofMul ((Additive.toMul x : rootsOfUnity n L) : Lˣ) :=
  rfl
noncomputable def kummerSequence : ShortComplex (Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :=
  ShortComplex.mk (rootsOfUnityToUnits K L n) (n • 𝟙 (galUnits.{u} K L)) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change n • Additive.ofMul
      (((Additive.toMul (α := rootsOfUnity n L) x : rootsOfUnity n L) : Lˣ)) = (0 : Additive Lˣ)
    rw [← ofMul_pow, (mem_rootsOfUnity n _).1 (Additive.toMul (α := rootsOfUnity n L) x).2,
      ofMul_one])
end Kummer
section Brauer
variable [IsGalois K L]
noncomputable abbrev galoisBrauerGroup : ModuleCat.{u} (ULift.{u} ℤ) :=
  cohomology (galUnits.{u} K L) 2
noncomputable abbrev cohomologicalBrauerGroup (Ksep : Type u) [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] : ModuleCat.{u} (ULift.{u} ℤ) :=
  galoisBrauerGroup K Ksep
end Brauer
section Inflation
variable {K L}
noncomputable def unitsRestrictHom (E : IntermediateField K L) [Normal K E] :
    Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E) (galUnits.{u} K E) ⟶
      galUnits.{u} K L :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Eˣ) (B := Additive Lˣ) (MonoidHom.toAdditive
    (Units.map ((algebraMap E L : E →+* L) : E →* L))), fun σ => by
    ext x
    exact AlgEquiv.restrictNormal_commutes σ E ((Additive.toMul (α := Eˣ) x : Eˣ) : E)⟩
theorem isLocallyConstant_unitsInflation (E : IntermediateField K L) [FiniteDimensional K E]
    [Normal K E] {n : ℕ} (x : (Fin n → Gal(E/K)) → Additive Eˣ) :
    IsLocallyConstant fun g : Fin n → Gal(L/K) =>
      (unitsRestrictHom E).hom (x fun i => AlgEquiv.restrictNormalHom E (g i)) :=
  (IsLocallyConstant.of_discrete fun y => (unitsRestrictHom E).hom (x y)).comp_continuous
    (continuous_pi fun i =>
      (InfiniteGalois.restrictNormalHom_continuous E).comp (continuous_apply i))
variable [IsGalois K L]
noncomputable def unitsInflationCochainsX (E : IntermediateField K L) [FiniteDimensional K E]
    [Normal K E] (n : ℕ) :
    (inhomogeneousCochains (galUnits.{u} K E)).X n ⟶ (cochainsComplex (galUnits.{u} K L)).X n :=
  ModuleCat.ofHom <| LinearMap.codRestrict (locallyConstantCochains _ n)
    ((groupCohomology.cochainsMap (AlgEquiv.restrictNormalHom E) (unitsRestrictHom E)).f n).hom
    fun x => (mem_locallyConstantCochains _ _).2 (isLocallyConstant_unitsInflation E x)
theorem unitsInflationCochainsX_comp_ι (E : IntermediateField K L) [FiniteDimensional K E]
    [Normal K E] (n : ℕ) :
    unitsInflationCochainsX E n ≫ (cochainsComplexι (galUnits.{u} K L)).f n =
      (groupCohomology.cochainsMap (AlgEquiv.restrictNormalHom E) (unitsRestrictHom E)).f n :=
  rfl
noncomputable def unitsInflationCochains (E : IntermediateField K L) [FiniteDimensional K E]
    [Normal K E] :
    inhomogeneousCochains (galUnits.{u} K E) ⟶ cochainsComplex (galUnits.{u} K L) where
  f n := unitsInflationCochainsX E n
  comm' i j _ := by
    rw [← cancel_mono ((cochainsComplexι (galUnits.{u} K L)).f j), Category.assoc,
      Category.assoc, ← (cochainsComplexι (galUnits.{u} K L)).comm i j, ← Category.assoc,
      unitsInflationCochainsX_comp_ι, unitsInflationCochainsX_comp_ι, HomologicalComplex.Hom.comm]
end Inflation
end GroundTheory.ProfCoh


