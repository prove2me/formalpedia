-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientDescendGrpObj
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientDescendGrpObj
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T19:42:43.117822+00:00
-- url     : https://prove2.me/theorems/9628790d-2f3c-4127-b4c0-be8b9eb87047
-- title:
--   Quotient Descend Grp Obj
-- statement:
--   Definitions and structural lemmas for Quotient Descend Grp Obj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/QuotientDescendGrpObj.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory
namespace QuotientDescent
variable {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} {G' : Over X'} {φ : G.left ⟶ G'.left}
noncomputable def up (H : IsPullback φ G.hom G'.hom π) {T : Over X'} (z : T ⟶ G') :
    (Over.pullback π).obj T ⟶ G :=
  Over.homMk (H.lift (pullback.fst T.hom π ≫ z.left) (pullback.snd T.hom π)
    (by rw [Category.assoc, Over.w, pullback.condition])) (H.lift_snd ..)
variable {Γ : Type} [Group Γ] [Finite Γ] {ρ : Γ →* Aut X} {τ : Γ →* Aut G.left}
def Equivariant (ρ : Γ →* Aut X) (τ : Γ →* Aut G.left) {T : Over X'}
    (w : (Over.pullback π).obj T ⟶ G) : Prop :=
  ∀ g (s : pullback T.hom π ⟶ pullback T.hom π), s ≫ pullback.fst T.hom π = pullback.fst T.hom π →
    s ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ (ρ g).hom →
    s ≫ w.left = w.left ≫ (τ g).hom
noncomputable def equivariantSubgroup [GrpObj G] (hτ : ∀ g, IsGrpPullback G G (ρ g).hom (τ g).hom)
    (T : Over X') : Subgroup ((Over.pullback π).obj T ⟶ G) :=
  ⨅ (g : Γ) (s : pullback T.hom π ⟶ pullback T.hom π)
    (_ : s ≫ pullback.fst T.hom π = pullback.fst T.hom π)
    (h : s ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ (ρ g).hom),
    (preHom (Over.homMk s h)).eqLocus (pushHom (hτ g) ((Over.pullback π).obj T))
end QuotientDescent
open QuotientDescent
end GlobalTheory


