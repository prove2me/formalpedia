-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CompEqIdOfTwists
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_CompEqIdOfTwists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:26.064975+00:00
-- url     : https://prove2.me/theorems/e1f93b02-1df8-405f-9f9d-18b00a02509d
-- title:
--   Comp Eq Id Of Twists
-- statement:
--   Definitions and structural lemmas for Comp Eq Id Of Twists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CompEqIdOfTwists.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
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
namespace GlobalTheory.Moduli.LevelAction
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
section Add
variable {L Q : Type} [AddCommGroup L] [Group Q] {w : L → Q}
end Add
section Obj
variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
end Obj
def Twists {l : Level H} (Xo : Moduli D l) (g : Sim D) (f : Xo.X ⟶ Xo.X) : Prop :=
  f ≫ Xo.s = Xo.s ∧ ∃ ν : SABMap Xo.univ.t Xo.univ.t f,
    (∀ a, (Xo.univ.eta (g.f l.M a)).left ≫ ν.φ = f ≫ (Xo.univ.eta a).left) ∧
    ∀ a, (Xo.univ.etaA (g.f l.A a)).left ≫ ν.φ = f ≫ (Xo.univ.etaA a).left
def lowerBase {l l₂ : Level H} (jK : KA l →+* KA l₂) : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := (baseKA l₂).ρ
  ρ_sq := (baseKA l₂).ρ_sq
  ζ := jK (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective jK.injective
end GlobalTheory.Moduli.LevelAction


