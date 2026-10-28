-- Prove2me | Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
-- name    : Sensitivity213981Formal_Supplement_NumericExpressions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T18:26:09.993998+00:00
-- url     : https://prove2.me/theorems/0801930a-85ee-4c5c-8bc2-90225d8fb3a0
-- title:
--   Supplement Numeric Expressions — sensitivity certificate definitions
-- statement:
--   The definitions for Numeric Expressions in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundNumeric.Expr.minimum`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; NumericExpressions.lean, lines 1–129.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NumericExpressions
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
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
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile









def Expr.minimum {n : ℕ} (first : Expr n) (es : List (Expr n)) : Expr n :=
  es.foldl .min first
































end ThreeBoundNumeric



end
end Sensitivity213981Formal


