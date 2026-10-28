-- Prove2me | Definitions.Def_Sensitivity213303_MinMaxNesting
-- name    : Sensitivity213303_MinMaxNesting
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:40:56.617523+00:00
-- url     : https://prove2.me/theorems/50422630-0ad5-4a68-bda1-4ed0c184c06b
-- title:
--   Order conditions ensuring nested min/max parent recipes
-- statement:
--   OrderedRecipe imposes the guard, tolerance and target-level order conditions on a min/max recipe. Guard levels and tolerances change in the direction needed for a stronger parent to imply a weaker one, and the lower and upper target levels satisfy monotonicity in the number of failed guards and the required order across parent levels. These finite conditions permit nestedness of child families to propagate through the recursive parent construction.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module MinMaxNesting; source SHA256 a818bfe7ba65fe756f4a27ada444c420f86ebb137da4e4441d8b058cd513609f.

import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace ThreeBoundNesting
open ThreeBoundWitness ThreeBoundProfiles

variable {L I V : Type} [Preorder L] [Fintype V]

/-- Conditions on an actual min/max recipe array that preserve the nesting of
the child predicates. They constrain recipes, not the desired output bound. -/
structure OrderedRecipe (r : MinMaxRecipe L V) : Prop where
  guard : Antitone r.guard
  tolerance : Antitone r.tolerance
  lower_mono : ∀ l, Monotone (r.lower l)
  upper_mono : ∀ l, Monotone (r.upper l)
  lower_order : ∀ i j, i ≤ j → ∀ b, b ≤ r.tolerance j →
    r.lower i b ≤ r.lower j b
  upper_order : ∀ i j, i ≤ j → ∀ b, b ≤ r.tolerance j →
    r.upper i b ≤ r.upper j b









end ThreeBoundNesting


