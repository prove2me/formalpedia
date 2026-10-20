-- Prove2me | Definitions.Def_MazurTransfer_OriginalContinuousScalarCharacterKernelRestrictionData20261019
-- name    : MazurTransfer_OriginalContinuousScalarCharacterKernelRestrictionData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T13:40:14.950492+00:00
-- url     : https://prove2.me/theorems/73ef8c7a-6d3f-441a-a407-7c398b134255
-- title:
--   Original scalar cocycle values and character-kernel action
-- statement:
--   Retain the original scalar value of a continuous cocycle and the intrinsic trivial-action certificate for the kernel of that same character. All field, group and topology parameters remain unchanged. The whole cocycle-value constructor and its generated structural proof helper are checked against the original module. Named downstream consumer: injectivity of restriction of continuous scalar-character cohomology and the genuine character-kernel maps for actual arithmetic classes.
-- source:
--   MazurTheorem ContinuousScalarCharacterKernelRestriction by Vas and contributors; original constructor and intrinsic subgroup-action certificate, with per-file Apache-2.0 attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original scalar cocycle-value constructor and its intrinsic trivial-action certificate on the same character kernel. All original field, group and topology contexts are retained; substantive restriction-injectivity proofs belong to the separate theorem submission.
Named downstream consumer: original scalar-character H1 restriction injectivity and genuine kernel-character maps for actual unramified character classes.
-/
import Definitions.Def_MazurTransfer_ScalarCharacterLineOriginalRepresentationsAndIntertwiningData20261018
import Definitions.Def_MazurTransfer_RepresentationDiscreteCoefficientsData
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologySubgroupRestrictionData
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: restrict the EXISTING continuous scalar-character H1
presentation to the kernel of that SAME character. Restriction is
injective, and this subgroup acts trivially on the given coefficients.
No finite group, finite image, splitting, or arithmetic input is assumed.
Named downstream consumer: the actual chi13 kernel-class arithmetic bound.
-/

noncomputable section
namespace MazurTransfer.ContinuousScalarCharacterKernelRestriction
open ScalarCharacterLine RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologySubgroupRestriction
variable {k G : Type} [Field k] [Group G] [TopologicalSpace G]
variable (χ : G →* kˣ)
local notation "M" => Coefficient (scalarRepresentation χ)

def cocycleValue (z : continuousCocycles G M) (g : G) : k :=
  (Additive.toMul (z.val g) : M).val



theorem kernel_action_trivial (s : χ.ker) (m : M) : s • m = m := by
  apply Coefficient.ext
  change (χ s.val : k) * m.val = m.val
  rw [show χ s.val = 1 from s.property, Units.val_one, one_mul]







end MazurTransfer.ContinuousScalarCharacterKernelRestriction
#print axioms MazurTransfer.ContinuousScalarCharacterKernelRestriction.cocycleValue
#print axioms MazurTransfer.ContinuousScalarCharacterKernelRestriction.kernel_action_trivial


