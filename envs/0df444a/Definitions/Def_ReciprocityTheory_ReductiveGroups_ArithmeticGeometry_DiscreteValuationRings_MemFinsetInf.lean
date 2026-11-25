-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_MemFinsetInf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_MemFinsetInf
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:32:32.044277+00:00
-- url     : https://prove2.me/theorems/e0157c7c-b417-5b55-b243-61c96498c1ef
-- title:
--   Mem Finset Inf
-- statement:
--   Definitions and structural lemmas for Mem Finset Inf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
def subSec {Y : Scheme.{0}} {M : LB Y} (s s' : LB.Sec M) : LB.Sec M where
  f j := s.f j - s'.f j
  compat i j := by rw [map_sub, map_sub, s.compat, s'.compat, mul_sub]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
def pullφB {D : DegPre V} {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O)
    (χ : D.X) : Fin 4 ⊕ Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  Sum.elim (DegPre.famφB D (star a • χ)) (fun i => (oa.onB.act a).left ≫ DegPre.famφB D χ i)
end ReciprocityTheory.ChartRestriction.G.DVR


