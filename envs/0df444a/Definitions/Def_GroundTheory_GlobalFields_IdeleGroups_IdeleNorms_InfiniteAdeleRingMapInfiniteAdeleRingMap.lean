-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_InfiniteAdeleRingMapInfiniteAdeleRingMap
-- name    : GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_InfiniteAdeleRingMapInfiniteAdeleRingMap
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:03.367917+00:00
-- url     : https://prove2.me/theorems/d354d43f-3dee-518e-9030-dc70f4db637f
-- title:
--   Infinite Adele Ring Map Infinite Adele Ring Map
-- statement:
--   Definitions and structural lemmas for Infinite Adele Ring Map Infinite Adele Ring Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/InfiniteAdeleRingMapInfiniteAdeleRingMap.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_completionMap_congr
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_apply
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_InfinitePlace_infiniteAdeleRingMap_apply
import Theorems.Thm_GroundTheory_Global_InfinitePlace_piPlacesOverEquiv_apply
import Theorems.Thm_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_ideleClassMap_mk
import Theorems.Thm_GroundTheory_Global_ideleClassNorm_mk
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
attribute [local simp] GroundTheory.Global.AdeleBaseChange.finiteTensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply
attribute [local simp] GroundTheory.Global.InfinitePlace.piPlacesOverEquiv_apply
attribute [local simp] GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingHomeomorph_apply
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.ideleClassMap_mk
attribute [local simp] GroundTheory.Global.ideleClassNorm_mk
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7


set_option autoImplicit false
namespace GroundTheory.Global
open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
namespace AdeleBaseChange
open SemiLocal
variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
theorem completionMap_completionMap (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (u : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal]
    [u.asIdeal.LiesOver v.asIdeal] (a : v.adicCompletion K) :
    completionMap w u (completionMap v w a) = completionMap v u a := by
  have h := (HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    ((continuous_completionMap w u).comp (continuous_completionMap v w))
    (continuous_completionMap v u) (funext fun k ↦ ?_)
  · exact congrFun h a
  · simp only [Function.comp_apply]
    rw [completionMap_algebraMap, completionMap_algebraMap,
      IsScalarTower.algebraMap_apply K L (w.adicCompletion L), completionMap_algebraMap,
      IsScalarTower.algebraMap_apply L M (u.adicCompletion M),
      IsScalarTower.algebraMap_apply K M (u.adicCompletion M), ← IsScalarTower.algebraMap_apply K L M]
omit [NumberField K] [NumberField L] [NumberField M] in

theorem below_below (u : HeightOneSpectrum (𝓞 M)) : below K (below L u) = below K u :=
  HeightOneSpectrum.ext (Ideal.under_under (A := 𝓞 K) (B := 𝓞 L) u.asIdeal)
theorem finiteAdeleMap_finiteAdeleMap (x : FiniteAdeleRing (𝓞 K) K) :
    finiteAdeleMap L M (finiteAdeleMap K L x) = finiteAdeleMap K M x := by
  refine FiniteAdeleRing.ext (K := M) fun u ↦ ?_
  have hb := below_below (K := K) (L := L) u
  have : u.asIdeal.LiesOver (below K (below L u)).asIdeal := by rw [hb]; infer_instance
  rw [finiteAdeleMap_apply, finiteAdeleMap_apply, finiteAdeleMap_apply,
    completionMap_completionMap (below K (below L u)) (below L u) u]
  exact completionMap_congr hb u x
omit [NumberField K] [NumberField L] [NumberField M] in

theorem algebraMap_completion_algebraMap (v : InfinitePlace K) (w : InfinitePlace L)
    (u : InfinitePlace M) [w.LiesOver v] [u.LiesOver w] [u.LiesOver v] (a : v.Completion) :
    algebraMap w.Completion u.Completion (algebraMap v.Completion w.Completion a) =
      algebraMap v.Completion u.Completion a := by
  have h := (InfinitePlace.Completion.denseRange_coe v).equalizer
    ((continuous_algebraMap w.Completion u.Completion).comp
      (continuous_algebraMap v.Completion w.Completion))
    (continuous_algebraMap v.Completion u.Completion) (funext fun y ↦ ?_)
  · exact congrFun h a
  · change algebraMap w.Completion u.Completion
        (algebraMap v.Completion w.Completion (algebraMap K v.Completion y.ofAbs)) =
      algebraMap v.Completion u.Completion (algebraMap K v.Completion y.ofAbs)
    rw [← IsScalarTower.algebraMap_apply K v.Completion w.Completion,
      ← IsScalarTower.algebraMap_apply K v.Completion u.Completion,
      IsScalarTower.algebraMap_apply K L w.Completion,
      ← IsScalarTower.algebraMap_apply L w.Completion u.Completion,
      IsScalarTower.algebraMap_apply L M u.Completion,
      IsScalarTower.algebraMap_apply K M u.Completion, ← IsScalarTower.algebraMap_apply K L M]
omit [NumberField K] [NumberField L] [NumberField M] [Algebra L M] [IsScalarTower K L M] in
theorem algebraMap_completion_congr {v v' : InfinitePlace K} (h : v = v') (u : InfinitePlace M)
    [u.LiesOver v] [u.LiesOver v'] (x : InfiniteAdeleRing K) :
    algebraMap v.Completion u.Completion (x v) = algebraMap v'.Completion u.Completion (x v') := by
  subst h
  rfl
omit [NumberField K] [NumberField L] [NumberField M] in

theorem infiniteAdeleRingMap_infiniteAdeleRingMap (x : InfiniteAdeleRing K) :
    GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := L) (L := M)
        (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := K) (L := L) x) =
      GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := K) (L := M) x := by
  funext u
  have hv : (u.comap (algebraMap L M)).comap (algebraMap K L) = u.comap (algebraMap K M) := by
    rw [IsScalarTower.algebraMap_eq K L M]
    rfl
  have : u.LiesOver ((u.comap (algebraMap L M)).comap (algebraMap K L)) := by
    rw [hv]; infer_instance
  rw [GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply,
    GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply,
    GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply,
    algebraMap_completion_algebraMap _ (u.comap (algebraMap L M)) u]
  exact algebraMap_completion_congr hv u x
theorem adeleMap_adeleMap (x : 𝔸[K]) : adeleMap L M (adeleMap K L x) = adeleMap K M x :=
  Prod.ext (infiniteAdeleRingMap_infiniteAdeleRingMap x.1) (finiteAdeleMap_finiteAdeleMap x.2)
scoped instance isScalarTower_adeleRing : IsScalarTower 𝔸[K] 𝔸[L] 𝔸[M] :=
  .of_algebraMap_eq fun x ↦ (adeleMap_adeleMap x).symm
end AdeleBaseChange
open AdeleBaseChange
variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
end
end GroundTheory.Global


