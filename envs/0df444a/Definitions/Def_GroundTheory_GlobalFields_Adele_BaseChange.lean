-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
-- name    : GroundTheory_GlobalFields_Adele_BaseChange
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:16:39.933706+00:00
-- url     : https://prove2.me/theorems/0bb26aa5-2b80-5d4b-9fa9-39e1a9ed48a9
-- title:
--   Base Change
-- statement:
--   Definitions and structural lemmas for Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleTensorEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleTensorEquiv_tmul
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_adeleMap
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_coord
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_finiteAdeleMap
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_finiteCoord
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_apply
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorEquiv_tmul
import Theorems.Thm_GroundTheory_Global_InfinitePlace_infiniteAdeleRingMap_apply
import Theorems.Thm_GroundTheory_Global_InfinitePlace_piPlacesOverEquiv_apply
import Theorems.Thm_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply
attribute [local simp] GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply
attribute [local simp] GroundTheory.Global.InfinitePlace.piPlacesOverEquiv_apply
attribute [local simp] GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingHomeomorph_apply
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7


set_option autoImplicit false
namespace GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
namespace AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
def tmulLeft (l : L) : 𝔸[K] →ₗ[𝔸[K]] L ⊗[K] 𝔸[K] where
  toFun x := l ⊗ₜ x
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' c x := by
    change l ⊗ₜ (c * x) = (1 ⊗ₜ c) * (l ⊗ₜ x)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
theorem adeleTensorEquiv_one_tmul_mul (a : 𝔸[K]) (t : L ⊗[K] 𝔸[K]) :
    adeleTensorEquiv K L ((1 ⊗ₜ a) * t) = adeleMap K L a * adeleTensorEquiv K L t := by
  rw [map_mul, adeleTensorEquiv_tmul, map_one, one_mul]
variable (K L) in

def adeleTensorSemilinear : L ⊗[K] 𝔸[K] →ₛₗ[adeleMap K L] 𝔸[L] where
  toFun := adeleTensorEquiv K L
  map_add' := map_add _
  map_smul' c t := adeleTensorEquiv_one_tmul_mul c t
variable (K L) in

def adeleTensorHomeomorph :
    letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
    L ⊗[K] 𝔸[K] ≃ₜ 𝔸[L] :=
  letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  haveI : IsModuleTopology 𝔸[K] (L ⊗[K] 𝔸[K]) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd 𝔸[K] (L ⊗[K] 𝔸[K])
  { toEquiv := (adeleTensorEquiv K L).toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMapₛₗ continuous_adeleMap (adeleTensorSemilinear K L)
    continuous_invFun := by
      have h : ∀ y, (adeleTensorEquiv K L).symm y =
          ∑ i, tmulLeft (Module.finBasis K L i) (coord (Module.finBasis K L) i y) :=
        adeleTensorEquiv_symm_apply (Module.finBasis K L)
      change Continuous fun y ↦ (adeleTensorEquiv K L).symm y
      simp_rw [h]
      exact continuous_finsetSum _ fun i _ ↦
        (IsModuleTopology.continuous_of_linearMap (tmulLeft (Module.finBasis K L i))).comp
          (continuous_coord _ i) }
@[simp]
theorem adeleTensorHomeomorph_apply (t : L ⊗[K] 𝔸[K]) :
    adeleTensorHomeomorph K L t = adeleTensorEquiv K L t :=
  rfl
variable (K L) in

def adeleTensorContinuousAlgEquiv :
    letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
    L ⊗[K] 𝔸[K] ≃A[L] 𝔸[L] :=
  letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  { adeleTensorEquiv K L with
    continuous_toFun := (adeleTensorHomeomorph K L).continuous_toFun
    continuous_invFun := (adeleTensorHomeomorph K L).continuous_invFun }
@[simp]
theorem adeleTensorContinuousAlgEquiv_apply (t : L ⊗[K] 𝔸[K]) :
    adeleTensorContinuousAlgEquiv K L t = adeleTensorEquiv K L t :=
  rfl
scoped instance algebraAdeleRing : Algebra 𝔸[K] 𝔸[L] :=
  (adeleMap K L).toAlgebra
scoped instance continuousSMul_adeleRing : ContinuousSMul 𝔸[K] 𝔸[L] :=
  continuousSMul_of_algebraMap _ _ continuous_adeleMap
variable (K L) in

def adeleTensorAlgEquivAdele : L ⊗[K] 𝔸[K] ≃ₐ[𝔸[K]] 𝔸[L] :=
  AlgEquiv.ofRingEquiv (f := (adeleTensorEquiv K L).toRingEquiv) fun a ↦ by
    change adeleTensorEquiv K L (1 ⊗ₜ a) = adeleMap K L a
    rw [adeleTensorEquiv_tmul, map_one, one_mul]
@[simp]
theorem adeleTensorAlgEquivAdele_apply (t : L ⊗[K] 𝔸[K]) :
    adeleTensorAlgEquivAdele K L t = adeleTensorEquiv K L t :=
  rfl
variable (K L) in

def adeleTensorContinuousAlgEquivAdele :
    letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
    L ⊗[K] 𝔸[K] ≃A[𝔸[K]] 𝔸[L] :=
  letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  { adeleTensorAlgEquivAdele K L with
    continuous_toFun := (adeleTensorHomeomorph K L).continuous_toFun
    continuous_invFun := (adeleTensorHomeomorph K L).continuous_invFun }
variable (K L) in

def normalizedTrace : L →ₗ[K] K :=
  (finrank K L : K)⁻¹ • Algebra.trace K L
variable (K L) in

def traceRetraction : L ⊗[K] 𝔸[K] →ₗ[𝔸[K]] 𝔸[K] where
  toFun t := TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L) t)
  map_add' s t := by simp only [map_add]
  map_smul' c t := by
    change _ = c * _
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      change TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L)
        ((1 ⊗ₜ c) * (l ⊗ₜ a))) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul, mul_smul_comm]
    | add s t hs ht => simp only [smul_add, map_add, hs, ht, mul_add]
variable (K L) in

def adeleRetraction (y : 𝔸[L]) : 𝔸[K] :=
  traceRetraction K L ((adeleTensorEquiv K L).symm y)
def finiteTmulLeft (l : L) :
    FiniteAdeleRing (𝓞 K) K →ₗ[FiniteAdeleRing (𝓞 K) K] L ⊗[K] FiniteAdeleRing (𝓞 K) K where
  toFun x := l ⊗ₜ x
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' c x := by
    change l ⊗ₜ (c * x) = (1 ⊗ₜ c) * (l ⊗ₜ x)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
variable (K L) in

def finiteTensorHomeomorph :
    letI := moduleTopology (FiniteAdeleRing (𝓞 K) K) (L ⊗[K] FiniteAdeleRing (𝓞 K) K)
    L ⊗[K] FiniteAdeleRing (𝓞 K) K ≃ₜ FiniteAdeleRing (𝓞 L) L :=
  letI := moduleTopology (FiniteAdeleRing (𝓞 K) K) (L ⊗[K] FiniteAdeleRing (𝓞 K) K)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 K) K) (L ⊗[K] FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 K) K)
    (L ⊗[K] FiniteAdeleRing (𝓞 K) K)
  { toEquiv := (finiteTensorEquiv K L).toEquiv
    continuous_toFun := by
      let φ : L ⊗[K] FiniteAdeleRing (𝓞 K) K →ₛₗ[finiteAdeleMap K L] FiniteAdeleRing (𝓞 L) L :=
        { toFun := finiteTensorEquiv K L
          map_add' := map_add _
          map_smul' := fun c t ↦ by
            change finiteTensorEquiv K L ((1 ⊗ₜ c) * t) = finiteAdeleMap K L c * _
            rw [map_mul, finiteTensorEquiv_tmul, map_one, one_mul] }
      exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_finiteAdeleMap φ
    continuous_invFun := by
      have h : ∀ y, (finiteTensorEquiv K L).symm y = ∑ i, finiteTmulLeft (Module.finBasis K L i)
          (finiteCoord (Module.finBasis K L) i y) :=
        finiteTensorEquiv_symm_apply (Module.finBasis K L)
      change Continuous fun y ↦ (finiteTensorEquiv K L).symm y
      simp_rw [h]
      exact continuous_finsetSum _ fun i _ ↦
        (IsModuleTopology.continuous_of_linearMap (finiteTmulLeft (Module.finBasis K L i))).comp
          (continuous_finiteCoord _ i) }
end AdeleBaseChange
end
end GroundTheory.Global


