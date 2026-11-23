-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:52.275313+00:00
-- url     : https://prove2.me/theorems/d19a67fd-d4e5-4175-8532-c124fb4ebcfa
-- title:
--   Free Yoneda Hom Equiv Free To Pullback Comp
-- statement:
--   Definitions and structural lemmas for Free Yoneda Hom Equiv Free To Pullback Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w w' w'' v u u₁ v₁ u₂ v₂
noncomputable section
namespace GlobalTheory
namespace SheafPull
section Abstract
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasExt.{w} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasExt.{w'} B]
  (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
def extMap {Z F : A} {Z' G : B} (a : Z' ⟶ Φ.obj Z) (b : Φ.obj F ⟶ G) (n : ℕ) :
    Ext.{w} Z F n →+ Ext.{w'} Z' G n :=
  ((Ext.mk₀ a).precomp G (zero_add n)).comp
    (((Ext.mk₀ b).postcomp (Φ.obj Z) (add_zero n)).comp (Φ.mapExtAddHom Z F n))
end Abstract
section Site
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  (p : C ⥤ D) [p.IsContinuous J K]
  [(p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]
open SheafLES
instance additive_sheafPullback : (p.sheafPullback AddCommGrpCat.{v} J K).Additive :=
  have := (p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).isLeftAdjoint
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (p.sheafPullback AddCommGrpCat.{v} J K)
  Functor.additive_of_preservesBinaryBiproducts _
instance preservesFiniteColimits_sheafPullback :
    PreservesFiniteColimits (p.sheafPullback AddCommGrpCat.{v} J K) :=
  have := (p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).isLeftAdjoint
  inferInstance
instance additive_sheafPushforwardContinuous :
    (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).Additive where
  map_add := rfl
variable (J K) in

def freeToPullback {V : C} {W : D} (i : W ⟶ p.obj V) :
    (freeYoneda K).obj W ⟶ (p.sheafPullback AddCommGrpCat.{v} J K).obj ((freeYoneda J).obj V) :=
  (freeYonedaHomEquiv W _).symm
    (((p.sheafPullback AddCommGrpCat.{v} J K).obj ((freeYoneda J).obj V)).obj.map i.op
      (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app _).hom.app (op V)
        (tautSection V)))
variable [PreservesFiniteLimits (p.sheafPullback AddCommGrpCat.{v} J K)]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{v})]
  {F F' : Sheaf J AddCommGrpCat.{v}} {G G' : Sheaf K AddCommGrpCat.{v}}
def sitePull (φ : F ⟶ (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj G) (n : ℕ)
    {V : C} {W : D} (i : W ⟶ p.obj V) : Sheaf.H'.{w} F n V →+ Sheaf.H'.{w'} G n W :=
  extMap.{w, w'} (p.sheafPullback AddCommGrpCat.{v} J K) (freeToPullback J K p i)
    (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ) n
end Site
end SheafPull
end GlobalTheory


