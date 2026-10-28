-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22NumericRecipe
-- name    : Sensitivity213981Formal_Endpoint22NumericRecipe
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:53:13.559856+00:00
-- url     : https://prove2.me/theorems/b0b35ef7-c45c-4b82-99f3-bb5b5425a0f0
-- title:
--   Endpoint22 Numeric Recipe — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Numeric Recipe in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxNumeric.Endpoint22.recipe`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22NumericRecipe.lean, lines 1–16.

import Definitions.Def_Sensitivity213981Formal_Endpoint22Recipes
import Definitions.Def_Sensitivity213981Formal_MinmaxExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Numeric entries are projections of the actual twenty-two-level recipes. -/


set_option autoImplicit false

namespace ThreeBoundMinmaxNumeric.Endpoint22

def recipe (p : Fin 4) (i : Fin 22) : Entry :=
  let e := Sensitivity5591Endpoint22.entry p i
  { lower := Array.ofFn (fun d : Fin 9 => (e.threshold d.val).val)
    upper := Array.ofFn (fun d : Fin 9 => (e.upper d.val).val)
    guard := e.guard.val
    tolerance := e.tolerance }

end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal


