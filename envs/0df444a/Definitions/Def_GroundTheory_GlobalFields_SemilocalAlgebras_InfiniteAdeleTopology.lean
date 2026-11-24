-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdeleTopology
-- name    : GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdeleTopology
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:08.412179+00:00
-- url     : https://prove2.me/theorems/b2f8a425-b72d-4028-a886-ca85b8f2e694
-- title:
--   Infinite Adele Topology
-- statement:
--   Definitions and structural lemmas for Infinite Adele Topology, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/InfiniteAdeleTopology.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdele
import Theorems.Thm_GroundTheory_Global_InfinitePlace_continuous_infiniteAdeleRingMap
import Theorems.Thm_GroundTheory_Global_InfinitePlace_infiniteAdeleRingMap_apply
import Theorems.Thm_GroundTheory_Global_InfinitePlace_piPlacesOverEquiv_apply
import Theorems.Thm_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingEquiv_tmul
import Theorems.Thm_P2M_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingEquiv_tmul__a0cdac9b4d94
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply
attribute [local simp] GroundTheory.Global.InfinitePlace.piPlacesOverEquiv_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
namespace InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
def piPlacesOverCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (v : InfinitePlace K) (i : ι) : PiPlacesOver (L := L) v →ₗ[v.Completion] v.Completion :=
  ((Algebra.TensorProduct.basis v.Completion b).coord i).comp
    (tensorPiEquiv (L := L) v).symm.toLinearMap
theorem continuous_piPlacesOverCoord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (v : InfinitePlace K) (i : ι) :
    Continuous (piPlacesOverCoord b v i) :=
  LinearMap.continuous_of_finiteDimensional _
theorem sum_piPlacesOverCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (v : InfinitePlace K) (y : PiPlacesOver (L := L) v) (w : v.placesOver L) :
    ∑ i, algebraMap v.Completion _ (piPlacesOverCoord b v i y) *
      (b i : (w : InfinitePlace L).Completion) = y w := by
  have h := (Algebra.TensorProduct.basis v.Completion b).sum_repr
    ((tensorPiEquiv (L := L) v).symm y)
  have h2 := congrArg (fun z => tensorPiEquiv (L := L) v z w) h
  simp only [AlgEquiv.apply_symm_apply] at h2
  rw [← h2, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, map_smul, Pi.smul_apply, tensorPiEquiv_apply,
    tensorPiHom_tmul, map_one, one_mul, Algebra.smul_def]
  rfl
def adeleCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L) (i : ι)
    (y : InfiniteAdeleRing L) : InfiniteAdeleRing K :=
  fun v => piPlacesOverCoord b v i (fun w => y w)
theorem continuous_adeleCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (i : ι) : Continuous (adeleCoord b i) :=
  continuous_pi fun v => (continuous_piPlacesOverCoord b v i).comp
    (continuous_pi fun w => continuous_apply (w : InfinitePlace L))
theorem tensorInfiniteAdeleRingEquiv_sum_adeleCoord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (y : InfiniteAdeleRing L) :
    tensorInfiniteAdeleRingEquiv (∑ i, b i ⊗ₜ[K] adeleCoord b i y) = y := by
  funext w
  have ev : ∀ f : ι → InfiniteAdeleRing L, (∑ i, f i) w = ∑ i, f i w := fun f =>
    map_sum (Pi.evalAddMonoidHom (fun w : InfinitePlace L => w.Completion) w) f Finset.univ
  rw [map_sum, ev]
  simp_rw [tensorInfiniteAdeleRingEquiv_tmul]
  have := sum_piPlacesOverCoord b (w.comap (algebraMap K L)) (fun w' => y w') ⟨w, liesOver_comap w⟩
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  rfl
def tmulLeft (l : L) : InfiniteAdeleRing K →ₗ[InfiniteAdeleRing K] L ⊗[K] InfiniteAdeleRing K where
  toFun x := l ⊗ₜ x
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' c x := by
    change l ⊗ₜ (c * x) = (1 ⊗ₜ c) * (l ⊗ₜ x)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
def tensorInfiniteAdeleRingHomeomorph :
    letI := moduleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
    L ⊗[K] InfiniteAdeleRing K ≃ₜ InfiniteAdeleRing L :=
  letI := moduleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  haveI : IsModuleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  let b := Module.finBasis K L
  { toEquiv := (tensorInfiniteAdeleRingEquiv (K := K) (L := L)).toEquiv
    continuous_toFun := by
      let φ : L ⊗[K] InfiniteAdeleRing K →ₛₗ[infiniteAdeleRingMap (K := K) (L := L)]
          InfiniteAdeleRing L :=
        { toFun := tensorInfiniteAdeleRingEquiv
          map_add' := map_add _
          map_smul' := fun c t => by
            change tensorInfiniteAdeleRingEquiv ((1 ⊗ₜ c) * t) = infiniteAdeleRingMap c * _
            rw [map_mul, tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul] }
      exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_infiniteAdeleRingMap φ
    continuous_invFun := by
      have h : ∀ y, (tensorInfiniteAdeleRingEquiv (K := K) (L := L)).symm y =
          ∑ i, tmulLeft (b i) (adeleCoord b i y) := fun y => by
        rw [AlgEquiv.symm_apply_eq]
        exact (tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y).symm
      change Continuous fun y => (tensorInfiniteAdeleRingEquiv (K := K) (L := L)).symm y
      simp_rw [h]
      exact continuous_finsetSum _ fun i _ =>
        (IsModuleTopology.continuous_of_linearMap (tmulLeft (b i))).comp
          (continuous_adeleCoord b i) }
end InfinitePlace
end GroundTheory.Global


