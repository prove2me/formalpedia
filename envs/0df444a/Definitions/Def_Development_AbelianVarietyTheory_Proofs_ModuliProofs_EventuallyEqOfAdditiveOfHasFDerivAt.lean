-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:24.777988+00:00
-- url     : https://prove2.me/theorems/29fb768a-3bf1-4c96-ab82-d89468aa6ea0
-- title:
--   Eventually Eq Of Additive Of Has FDeriv At
-- statement:
--   Definitions and structural lemmas for Eventually Eq Of Additive Of Has FDeriv At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EventuallyEqOfAdditiveOfHasFDerivAt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace GlobalTheory.RelExp
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {Z Y : Scheme.{0}}
def HolAt (a : E → (Sp ℂ ⟶ Z)) (w₀ : E) : Prop := ∃ W, IsOpen W ∧ w₀ ∈ W ∧ IsHolTo W a
namespace HolAt
variable {a a' : E → (Sp ℂ ⟶ Z)} {w₀ : E}
end HolAt
section Group
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {y : E → (Sp ℂ ⟶ X)} {w₀ : E}
end Group
section Additive
variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup A]
end Additive
end GlobalTheory.RelExp


