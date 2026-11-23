-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CorrOfGenericOfIsSeparated
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CorrOfGenericOfIsSeparated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:31.34881+00:00
-- url     : https://prove2.me/theorems/dbd6c488-0ca0-4d8b-af3a-f5c463cd658b
-- title:
--   Corr Of Generic Of Is Separated
-- statement:
--   Definitions and structural lemmas for Corr Of Generic Of Is Separated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CorrOfGenericOfIsSeparated.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory
universe u
namespace DoubledPoint
variable {X : Scheme.{0}} (U : X.Opens)
instance {i j : WalkingSpan} (f : i ⟶ j) : IsOpenImmersion ((span U.ι U.ι).map f) := by
  rcases f with _ | (_ | _) <;> (dsimp; infer_instance)
abbrev signLB (Y : Scheme.{0}) : LB Y where
  ι := Bool
  U := fun _ => ⊤
  g := fun i j => if i = j then 1 else -1
def signGen {Y T : Scheme.{0}} (f : T ⟶ Y) : LB.Gen ((signLB Y).pull f) where
  s := fun j => cond (j PUnit.unit) 1 (-1)
end DoubledPoint
end GlobalTheory


