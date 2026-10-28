-- Prove2me | Definitions.Def_Sensitivity213981Formal_NatTableChecks
-- name    : Sensitivity213981Formal_NatTableChecks
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:08:47.879025+00:00
-- url     : https://prove2.me/theorems/c8fcf1e0-384e-4044-812f-6aaf8125e68c
-- title:
--   Nat Table Checks — sensitivity certificate definitions
-- statement:
--   The definitions for Nat Table Checks in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundNumeric.NatTable.lowerCheck`, `ThreeBoundNumeric.NatTable.dominates`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; NatTableChecks.lean, lines 1–85.

import Definitions.Def_Sensitivity213981Formal_FlatProfiles
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Small structural checks for globally ordered piecewise constant tables. -/


set_option autoImplicit false

namespace ThreeBoundNumeric.NatTable



def lowerCheck (bound : ℕ) : NatTable → Bool
  | .leaf v => bound≤ v
  | .branch _ left right => lowerCheck bound left && lowerCheck bound right



/-- The two trees use the same cuts whenever both nodes branch. A leaf may
represent an arbitrarily large constant interval. No interval endpoints need
to be supplied or trusted. -/
def dominates (factor : ℕ) : NatTable → NatTable → Bool
  | .leaf a, .leaf b => a≤ factor*b
  | .leaf a, .branch _ left right =>
      dominates factor (.leaf a) left && dominates factor (.leaf a) right
  | .branch _ left right, .leaf b =>
      dominates factor left (.leaf b) && dominates factor right (.leaf b)
  | .branch ca la ra, .branch cb lb rb =>
      ca==cb && dominates factor la lb && dominates factor ra rb
termination_by a b => sizeOf a+sizeOf b



end ThreeBoundNumeric.NatTable



end
end Sensitivity213981Formal


