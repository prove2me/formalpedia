-- Prove2me | Definitions.Def_Sensitivity213981Formal_Packed5591Check40
-- name    : Sensitivity213981Formal_Packed5591Check40
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:09:22.832781+00:00
-- url     : https://prove2.me/theorems/6ff7ea89-2d10-4ca9-8e24-81a17b7b4a4d
-- title:
--   Packed5591 Check40 — sensitivity certificate definitions
-- statement:
--   The definitions for Packed5591 Check40 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Packed.checked_40`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Packed5591Check40.lean, lines 1–11.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Packed5591Data
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Init.Data.Nat.Bitwise.Lemmas
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
set_option exponentiation.threshold 200000
namespace Sensitivity5591Packed

theorem checked_40:checkRange 5120 128=true:=by decide +kernel
end Sensitivity5591Packed


end
end Sensitivity213981Formal


