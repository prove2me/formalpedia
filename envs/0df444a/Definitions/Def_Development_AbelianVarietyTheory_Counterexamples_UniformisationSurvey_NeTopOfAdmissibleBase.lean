-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UniformisationSurvey_NeTopOfAdmissibleBase
-- name    : Development_AbelianVarietyTheory_Counterexamples_UniformisationSurvey_NeTopOfAdmissibleBase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:50.91909+00:00
-- url     : https://prove2.me/theorems/ef397b4f-ff29-42f2-8fa7-9238cfd7b77f
-- title:
--   Ne Top Of Admissible Base
-- statement:
--   Definitions and structural lemmas for Ne Top Of Admissible Base, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/NeTopOfAdmissibleBase.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsAddEquivOfSplitTorusIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.LinearUnifCheck
section Torus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
end Torus
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
  {O : Type} [Ring O] [StarRing O] {D : DegData R I} [Module O D.toPre.X]
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O)
end GlobalTheory.LinearUnifCheck


