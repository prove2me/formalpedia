-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsPullCubicalOfGenericOfExt
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsPullCubicalOfGenericOfExt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:22.223732+00:00
-- url     : https://prove2.me/theorems/536b2ec9-690e-5860-86a4-c12ebfc591ea
-- title:
--   Is Pull Cubical Of Generic Of Ext
-- statement:
--   Definitions and structural lemmas for Is Pull Cubical Of Generic Of Ext, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsPullCubicalOfGenericOfExt.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SabMapOfIsoOfExtendGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChartCubExt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Exist.CubicalExtension
def ExtendGenAt (V K : Type) [CommRing V] [Field K] [Algebra V K] : Prop :=
  ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (eA : Sp K ⟶ pullback G.hom (spMap (algebraMap V K))),
      eA ≫ pullback.fst G.hom (spMap (algebraMap V K)) = spMap (algebraMap V K) ≫ eSec G →
    ∀ (N : RigLB G) (r : LB.Gen (N.L.pull (pullback.fst G.hom (spMap (algebraMap V K))))), r.IsGen →
    LB.Gen.Corr N.L _ _ _ _ (LB.pullGen N.L _ _ r eA) (LB.pullGen N.L _ _ N.rig (spMap (algebraMap V K))) →
    ∃ r' : LB.Gen N.L, r'.IsGen ∧ LB.genPull N.L r' (pullback.fst G.hom (spMap (algebraMap V K))) = r
section Group
variable {T K : Type} [CommRing T] [IsDomain T] [Field K] [Algebra T K] [IsFractionRing T K]
end Group
end GlobalTheory.ChartCubExt


