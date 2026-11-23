-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTangentLift
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTangentLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:55.162526+00:00
-- url     : https://prove2.me/theorems/cf3fb418-f028-4432-bde7-0ab095089d58
-- title:
--   Exists Unique Tangent Lift
-- statement:
--   Definitions and structural lemmas for Exists Unique Tangent Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTangentLift.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.LieEtale
section Formal
variable {S : Scheme.{0}} {O k : Type} {P E : Over S}
def Eig {G : Over S} [GrpObj G] (z : P ⟶ E) (sc : k → (E ⟶ E)) (act : O → (G ⟶ G)) (τ : O → k)
    (v : E ⟶ G) : Prop :=
  z ≫ v = 1 ∧ ∀ a, v ≫ act a = sc (τ a) ≫ v
end Formal
section Dual
variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S)
def epsPtZero : Over.mk x ⟶ epsPt x :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (by
    change _ ≫ _ ≫ x = x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) =
      RingHom.id k := RingHom.ext fun _ => rfl
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp])
def epsPtScale (c : k) : epsPt x ⟶ epsPt x :=
  Over.homMk (spMap (epsScale c)) (by
    change _ ≫ _ ≫ x = _ ≫ x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).commutes r)
variable {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (τ : O →+* k)
end Dual
end GlobalTheory.LieEtale


