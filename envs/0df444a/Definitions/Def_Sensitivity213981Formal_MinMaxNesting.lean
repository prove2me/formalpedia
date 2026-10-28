-- Prove2me | Definitions.Def_Sensitivity213981Formal_MinMaxNesting
-- name    : Sensitivity213981Formal_MinMaxNesting
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T19:30:52.201062+00:00
-- url     : https://prove2.me/theorems/f43ff52d-61ad-4145-b804-e7c702e627aa
-- title:
--   Min Max Nesting — sensitivity certificate definitions
-- statement:
--   The definitions for Min Max Nesting in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundNesting.OrderedRecipe`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinMaxNesting.lean, lines 1–78.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_ProfileClosures
import Definitions.Def_Sensitivity213981Formal_RecursiveLowerBounds
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Sensitivity213981Formal
section


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
  lower_order : ∀ i j, i ≤  j → ∀ b, b ≤  r.tolerance j →
    r.lower i b ≤  r.lower j b
  upper_order : ∀ i j, i ≤  j → ∀ b, b ≤  r.tolerance j →
    r.upper i b ≤  r.upper j b









end ThreeBoundNesting




end
end Sensitivity213981Formal


