-- Prove2me | Definitions.Def_OAIQ253P010
-- name    : OAIQ253P010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T06:11:54.618484+00:00
-- url     : https://prove2.me/theorems/8135323b-11f7-4c16-ac32-ac6168f8493b
-- title:
--   Definitions bundle OAIQ253P010 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.PartitionPilot.Forcing.TransitiveGround.orbitTopPairsDefinition`, `OAI.PartitionPilot.Forcing.TransitiveGround.profileImageDefinition`, `OAI.PartitionPilot.Forcing.TransitiveGround.selectedJointDefinition`.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory, in whole or in part: [`PartitionPrinciple_Forcing_GroundSelectedOrbitNameFamilies`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Forcing/GroundSelectedOrbitNameFamilies.lean), [`PartitionPrinciple_Geometry_GroundCertificateProfileImageFamilies`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Geometry/GroundCertificateProfileImageFamilies.lean).
--
--   **Imports.** It imports the published bundle `Def_PartitionPrinciple`; the bundles `OAIQ253P007` and `OAIQ253P008` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_compatible_insertion_unions`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticBinaryRow_ordinal_partial_cover` and `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_insertion_crossCollisions`.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); definitions carved from lean/OAI/SetTheory at commit 7ef5c0c

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P007
import Definitions.Def_OAIQ253P008

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSelectedOrbitNameFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

noncomputable def orbitTopPairsDefinition
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => ZFSet.prod (env 0) {env 1}) := by
  let v := GroundSetTerm.var M (n := 2)
  let singleton := GroundSetTerm.app (M.definable_singleton pairing) ![v 1]
  exact (GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 0, singleton]).definition

end TransitiveGround
end PartitionPilot.Forcing




namespace PartitionPilot.Forcing
namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

noncomputable def selectedJointDefinition
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 4 → ZFSet.{u} =>
      orderedPairNameCode (env 1) (⋃₀ relationImage {env 0} (env 2) (env 3)) (env 0)) := by
  let v := GroundSetTerm.var M (n := 4)
  let input := GroundSetTerm.app (M.definable_singleton pairing) ![v 0]
  let image := GroundSetTerm.app (selectedImageDefinition M separation) ![input, v 2, v 3]
  let selected := GroundSetTerm.app (M.definable_sUnion unions) ![image]
  exact (GroundSetTerm.app (jointCodeDefinition M pairing) ![v 1, selected, v 0]).definition

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCertificateProfileImageFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def profileImageDefinition
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 5 → ZFSet.{u} =>
      relationImage (env 1) (env 3)
        (relationCompose (env 1) (env 2) (env 3) (env 0) (env 4))) := by
  let v := GroundSetTerm.var M (n := 5)
  let composed := GroundSetTerm.app (M.definable_relationCompose pairing unions powers separation)
    ![v 1, v 2, v 3, v 0, v 4]
  exact (GroundSetTerm.app (profileRelationImageDefinition M separation)
    ![v 1, v 3, composed]).definition

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end


