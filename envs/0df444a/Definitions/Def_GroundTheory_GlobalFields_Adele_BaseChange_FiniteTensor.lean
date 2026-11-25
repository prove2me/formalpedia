-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
-- name    : GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:29:28.080805+00:00
-- url     : https://prove2.me/theorems/bb41e4aa-b74a-4818-aa83-25a606f32c37
-- title:
--   Finite Tensor
-- statement:
--   Definitions and structural lemmas for Finite Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteTensor.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_completionMap_congr
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_algebraMap
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_apply
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_localCoord_algebraMap
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_localCoord_mem
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_sum_localCoord
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
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7


set_option autoImplicit false
namespace GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
namespace AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
def evalAddHom (w : HeightOneSpectrum (𝓞 L)) : FiniteAdeleRing (𝓞 L) L →+ w.adicCompletion L where
  toFun y := y w
  map_zero' := rfl
  map_add' _ _ := rfl
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
theorem eventually_localCoord_mem (i : ι) (y : FiniteAdeleRing (𝓞 L) L) :
    ∀ᶠ v in cofinite, localCoord b v i (fun w ↦ y w.1) ∈ v.adicCompletionIntegers K := by
  have hfin : {w : HeightOneSpectrum (𝓞 L) |
      ¬ (y * algebraMap L (FiniteAdeleRing (𝓞 L) L) (traceDual b i)) w ∈
        w.adicCompletionIntegers L}.Finite :=
    Filter.eventually_cofinite.1 (y * algebraMap L (FiniteAdeleRing (𝓞 L) L) (traceDual b i)).2
  refine Filter.eventually_cofinite.2 ((hfin.image (below K)).subset fun v hv ↦ ?_)
  by_contra hv'
  refine hv (localCoord_mem b v i _ fun w ↦ ?_)
  by_contra hw
  exact hv' ⟨w.1, hw, (below_eq_iff w.1 v).2 w.2⟩
def finiteCoord (i : ι) : FiniteAdeleRing (𝓞 L) L →+ FiniteAdeleRing (𝓞 K) K where
  toFun y := ⟨fun v ↦ localCoord b v i (fun w ↦ y w.1), eventually_localCoord_mem b i y⟩
  map_zero' := FiniteAdeleRing.ext (K := K) fun v ↦ map_zero (localCoord b v i)
  map_add' y y' := FiniteAdeleRing.ext (K := K) fun v ↦
    map_add (localCoord b v i) (fun w : PlacesOver L v ↦ y w.1) (fun w : PlacesOver L v ↦ y' w.1)
theorem finiteCoord_apply (i : ι) (y : FiniteAdeleRing (𝓞 L) L) (v : HeightOneSpectrum (𝓞 K)) :
    finiteCoord b i y v = localCoord b v i (fun w ↦ y w.1) :=
  rfl
local instance _p2m_local_instance_431a99de7f_75 : Algebra K (FiniteAdeleRing (𝓞 L) L) :=
  ((algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap K L)).toAlgebra
local instance _p2m_local_instance_431a99de7f_78 : IsScalarTower K L (FiniteAdeleRing (𝓞 L) L) :=
  .of_algebraMap_eq fun _ ↦ rfl
variable (K L) in

def finiteTensorMap : L ⊗[K] FiniteAdeleRing (𝓞 K) K →ₐ[L] FiniteAdeleRing (𝓞 L) L :=
  Algebra.TensorProduct.lift (Algebra.ofId L _)
    { finiteAdeleMap K L with commutes' := finiteAdeleMap_algebraMap } fun _ _ ↦ Commute.all _ _
theorem finiteTensorMap_tmul (l : L) (a : FiniteAdeleRing (𝓞 K) K) :
    finiteTensorMap K L (l ⊗ₜ a) = algebraMap L _ l * finiteAdeleMap K L a := by
  rw [finiteTensorMap, Algebra.TensorProduct.lift_tmul]
  rfl
theorem finiteCoord_algebraMap_mul (i : ι) (l : L) (a : FiniteAdeleRing (𝓞 K) K) :
    finiteCoord b i (algebraMap L _ l * finiteAdeleMap K L a) =
      algebraMap K _ (b.repr l i) * a := by
  refine FiniteAdeleRing.ext (K := K) fun v ↦ ?_
  rw [finiteCoord_apply]
  have : (fun w : PlacesOver L v ↦
      (algebraMap L (FiniteAdeleRing (𝓞 L) L) l * finiteAdeleMap K L a) w.1) =
      a v • algebraMap L (CompletionsOver L v) l := by
    funext w
    change algebraMap L (w.1.adicCompletion L) l *
        completionMap (below K w.1) w.1 (a (below K w.1)) =
      completionMap v w.1 (a v) * algebraMap L (w.1.adicCompletion L) l
    rw [completionMap_congr ((below_eq_iff w.1 v).2 w.2), mul_comm]
  rw [this, map_smul, localCoord_algebraMap, smul_eq_mul, mul_comm]
  rfl
theorem finiteTensorMap_sum_finiteCoord (y : FiniteAdeleRing (𝓞 L) L) :
    finiteTensorMap K L (∑ i, b i ⊗ₜ finiteCoord b i y) = y := by
  refine FiniteAdeleRing.ext (K := L) fun w ↦ ?_
  rw [map_sum]
  change evalAddHom w (∑ i, finiteTensorMap K L (b i ⊗ₜ finiteCoord b i y)) = y w
  rw [map_sum]
  have h := congrFun (sum_localCoord b (below K w) (fun w' ↦ y w'.1)) ⟨w, liesOver_below w⟩
  rw [Finset.sum_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [finiteTensorMap_tmul]
  exact mul_comm _ _
theorem sum_finiteCoord_finiteTensorMap (t : L ⊗[K] FiniteAdeleRing (𝓞 K) K) :
    ∑ i, b i ⊗ₜ finiteCoord b i (finiteTensorMap K L t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
    simp_rw [finiteTensorMap_tmul, finiteCoord_algebraMap_mul, ← Algebra.smul_def,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← TensorProduct.sum_tmul, b.sum_repr]
  | add s t hs ht =>
    simp_rw [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hs, ht]
variable (K L) in

def finiteTensorEquiv : L ⊗[K] FiniteAdeleRing (𝓞 K) K ≃ₐ[L] FiniteAdeleRing (𝓞 L) L :=
  AlgEquiv.ofBijective (finiteTensorMap K L)
    ⟨Function.LeftInverse.injective
      (g := fun y : FiniteAdeleRing (𝓞 L) L ↦ ∑ i, Module.finBasis K L i ⊗ₜ finiteCoord (Module.finBasis K L) i y)
      (sum_finiteCoord_finiteTensorMap (Module.finBasis K L)),
    Function.RightInverse.surjective (finiteTensorMap_sum_finiteCoord (Module.finBasis K L))⟩
end AdeleBaseChange
end
end GroundTheory.Global


