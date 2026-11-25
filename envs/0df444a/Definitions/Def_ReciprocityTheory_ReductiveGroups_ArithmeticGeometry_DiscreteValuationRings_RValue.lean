-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T14:16:33.646331+00:00
-- url     : https://prove2.me/theorems/4b1287da-abd2-4fb8-a2fa-e2cf3763fff3
-- title:
--   RValue
-- statement:
--   Definitions and structural lemmas for RValue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RValue.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
def rFac (oa : D.toPre.OAct O) (a : O)
    (uR : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (χ : D.toPre.X) :=
  LB.pullGen D.toPre.P.L _ _ uR (lift (cPB D F χ) (DegPre.prB D.toPre F)).left
def zc (mu : D.toPre.X) : (TF (R := V) F).left ⟶ (DegPre.BF D.toPre F).left :=
  (lift (𝟙 _) (toUnit _ ≫ D.toPre.c mu) : TF (R := V) F ⟶ DegPre.BF D.toPre F).left
end ReciprocityTheory.ChartRestriction.G.DVR


