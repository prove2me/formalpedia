-- Prove2me | Definitions.Def_MazurTransfer_OriginalContinuousScalarKernelCharacterMapsData20261019
-- name    : MazurTransfer_OriginalContinuousScalarKernelCharacterMapsData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-20T18:38:33.166333+00:00
-- url     : https://prove2.me/theorems/64ddf548-555a-430a-9516-f5eba840ee4c
-- title:
--   Original genuine continuous kernel character maps
-- statement:
--   Retain the original continuous character map of the same scalar-character kernel and its conjugation constructor. The two complete types, two whole constructor values and four generated structural proof types are checked against the original module. Named downstream consumer: injectivity, covariance and local vanishing of the same kernel character map, and the actual arithmetic unramified character embedding.
-- source:
--   MazurTheorem ContinuousScalarKernelCharacters by Vas and contributors; original kernel character and conjugation constructors, with per-file Apache-2.0 attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original map from continuous scalar-character H1 to genuine continuous characters of the same character kernel, and conjugation inside that kernel. Injectivity, covariance and local vanishing are separate downstream theorems.
Named downstream consumer: the actual unramified character-kernel embedding for the fixed arithmetic character.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousScalarCharacterKernelRestrictionData20261019
import Definitions.Def_MazurTransfer_OriginalTrivialContinuousCohomologyCharacterMapData20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inject scalar-character continuous H1 into GENUINE
continuous characters of the SAME character kernel. Preserve conjugation
covariance and vanishing on intersections with each given local subgroup.
Named downstream consumer: actual reflected-character arithmetic Selmer
classes, retaining all genuine valuation inertia conditions.
-/

noncomputable section
namespace MazurTransfer.ContinuousScalarKernelCharacters
open ScalarCharacterLine RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologySubgroupRestriction
open ContinuousScalarCharacterKernelRestriction
variable {k G : Type} [Field k] [Group G] [TopologicalSpace G]
variable (χ : G →* kˣ)
local notation "M" => Coefficient (scalarRepresentation χ)

def kernelCharacters : H1 G M →+ Additive (χ.ker →ₜ* M) :=
  (TrivialContinuousH1Characters.toHom χ.ker M (kernel_action_trivial χ)).comp
    (restriction G M χ.ker)





def conjugateKernelElement (g : G) (s : χ.ker) : χ.ker :=
  ⟨g * s.val * g⁻¹, by
    change χ (g * s.val * g⁻¹) = 1
    rw [map_mul, map_mul, map_inv, s.property, mul_one, mul_inv_cancel]⟩









end MazurTransfer.ContinuousScalarKernelCharacters
#print axioms MazurTransfer.ContinuousScalarKernelCharacters.kernelCharacters
#print axioms MazurTransfer.ContinuousScalarKernelCharacters.conjugateKernelElement


