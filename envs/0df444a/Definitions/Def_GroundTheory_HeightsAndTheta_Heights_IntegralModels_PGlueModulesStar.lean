-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:39.719381+00:00
-- url     : https://prove2.me/theorems/f75b6267-dd60-4a95-8367-4e2e2794b5a3
-- title:
--   PGlue Modules Star
-- statement:
--   Definitions and structural lemmas for PGlue Modules Star, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace GlueModulesStar
section Multi
abbrev starShape (ι : Type*) : MulticospanShape where
  L := Option ι
  R := ι
  fst := fun _ => none
  snd := some
variable {C : Type*} [Category C] {ι : Type*}
end Multi
section Sheaf
universe u
open Scheme.Modules in

def transMap {A B Z : Scheme.{u}} (f : A ⟶ B) (h : B ⟶ Z) {k : A ⟶ Z} (e : f ≫ h = k)
    {M : B.Modules} {N : A.Modules} (χ : (Scheme.Modules.pullback f).obj M ⟶ N) :
    (pushforward h).obj M ⟶ (pushforward k).obj N :=
  (pushforward h).map ((pullbackPushforwardAdjunction f).homEquiv _ _ χ) ≫
    (pushforwardComp f h).hom.app N ≫ (pushforwardCongr e).hom.app N
end Sheaf
section Glue
universe u
variable {X : Scheme.{u}} (V : X.Opens) {ι : Type u} (U : ι → X.Opens)
  (G : (V : Scheme.{u}).Modules) (F : ∀ i, (U i : Scheme.{u}).Modules)
  (ψ : ∀ i, (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U i ⊓ V ≤ U i))).obj (F i) ≅
    (Scheme.Modules.pullback (X.homOfLE (inf_le_right : U i ⊓ V ≤ V))).obj G)
def index : MulticospanIndex (starShape ι) X.Modules where
  left a := match a with
    | none => (Scheme.Modules.pushforward V.ι).obj G
    | some i => (Scheme.Modules.pushforward (U i).ι).obj (F i)
  right i := (Scheme.Modules.pushforward (U i ⊓ V).ι).obj
    ((Scheme.Modules.pullback (X.homOfLE (inf_le_right : U i ⊓ V ≤ V))).obj G)
  fst i := transMap (X.homOfLE (inf_le_right : U i ⊓ V ≤ V)) V.ι (X.homOfLE_ι _) (𝟙 _)
  snd i := transMap (X.homOfLE (inf_le_left : U i ⊓ V ≤ U i)) (U i).ι (X.homOfLE_ι _) (ψ i).hom
end Glue
end GlueModulesStar
end
end GroundTheory.Heights₂.Heights.Model


