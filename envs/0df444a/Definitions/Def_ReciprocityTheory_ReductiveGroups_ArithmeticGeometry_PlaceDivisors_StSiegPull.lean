-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StSiegPull
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StSiegPull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:31.022251+00:00
-- url     : https://prove2.me/theorems/1727f524-465f-4a6b-9793-c1a2f194033d
-- title:
--   St Sieg Pull
-- statement:
--   Definitions and structural lemmas for St Sieg Pull, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/StSiegPull.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ReciprocityTheory.ChartRestriction.G.Pdiv
structure SiegPairPB {S S' : Scheme.{0}} {h M₁ : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}
    (o : SiegPre h M₁ ζ s) (f : S' ⟶ S) where
  A : Over S'
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  φ : A.left ⟶ o.A.left
  φ₂ : (G2 A).left ⟶ (G2 o.A).left
  pb : IsGrpPullback A o.A f φ
  sq : IsSquare φ φ₂
  P : LB (G2 A).left
  isLB : P.IsLB
  iso : LBIso P (o.P.pull φ₂)
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)
attribute [instance] SiegPairPB.grp SiegPairPB.comm
def StSiegPull : Prop :=
  ∀ {S S' : Scheme.{0}} {h M₁ : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}
    (o : SiegPre h M₁ ζ s) (f : S' ⟶ S), Nonempty (SiegPairPB o f)
end ReciprocityTheory.ChartRestriction.G.Pdiv


