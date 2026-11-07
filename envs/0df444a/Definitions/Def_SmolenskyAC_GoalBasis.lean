-- Prove2me | Definitions.Def_SmolenskyAC_GoalBasis
-- name    : SmolenskyAC_GoalBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:10.74827+00:00
-- url     : https://prove2.me/theorems/5dd06015-408c-4a59-aea8-510d9b2e6fe8
-- title:
--   The basis AND, OR, NOT, $\mathrm{MOD}_p$ of Theorem 2, with AND and OR counted
-- statement:
--   The gate kinds of Theorem 2 are AND, OR, NOT and $\mathrm{MOD}_p$, interpreted by the operations of the same names for a fixed modulus $p$. The kinds AND and OR are flagged: Theorem 2 counts only AND and OR gates, while NOT and $\mathrm{MOD}_p$ gates are free.
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, Theorem 2, p.81 (pdf 5)

import Mathlib
import Definitions.Def_SmolenskyAC_Operations

namespace SmolenskyAC

/-- The basic operations of Theorem 2 (Smolensky, STOC 1987, Theorem 2, p.81): AND, OR, NOT and
`MOD_p`. -/
inductive GoalKind where
  | and
  | or
  | not
  | modp
  deriving DecidableEq

/-- The interpretation of the gate kinds of Theorem 2, for the modulus `p`. -/
def goalOp (p : ℕ) : GoalKind → Operation
  | .and => AND
  | .or => OR
  | .not => NOT
  | .modp => MODp p

/-- The gates Theorem 2 counts: AND and OR. NOT and `MOD_p` gates are free (p.81, "requires … AND
and OR gates"). -/
def goalFlag : GoalKind → Bool
  | .and => true
  | .or => true
  | .not => false
  | .modp => false

end SmolenskyAC


