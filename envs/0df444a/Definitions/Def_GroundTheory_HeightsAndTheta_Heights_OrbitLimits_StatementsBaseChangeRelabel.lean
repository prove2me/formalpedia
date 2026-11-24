-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBaseChangeRelabel
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBaseChangeRelabel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:10.120272+00:00
-- url     : https://prove2.me/theorems/3b7d98df-bfc6-4f65-83dc-62e35b4b3714
-- title:
--   Statements Base Change Relabel
-- statement:
--   Definitions and structural lemmas for Statements Base Change Relabel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsBaseChangeRelabel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.AI.I1
universe u u' v w v' w'
def BaseChangeRelabel.Statement : Prop :=
  ∀ (F : Type u) [Field F] (F' : Type u') [Field F'] [Algebra F F'] (K : Type v) [Fintype K]
    (ι : K → Type w) [∀ k, Fintype (ι k)] (K' : Type v') [Fintype K'] (ι' : K' → Type w')
    [∀ k, Fintype (ι' k)] (e : K ≃ K'),
    (∀ k, ι k ≃ ι' (e k)) → BaseChangeStatement F F' ι' → BaseChangeStatement F F' ι
def BaseChangeRelabel.renaming_example :
    (PUnit.{2} ≃ Unit) ×
      (∀ k : PUnit.{2}, ULift.{1} (Fin 2) ≃ (fun _ : Unit => Fin 2) (Equiv.punitEquivPUnit k)) :=
  ⟨Equiv.punitEquivPUnit, fun _ => Equiv.ulift⟩
end GroundTheory.Heights₂.Heights.Targets


