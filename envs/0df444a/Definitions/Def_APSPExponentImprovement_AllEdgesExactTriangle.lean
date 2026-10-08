-- Prove2me | Definitions.Def_APSPExponentImprovement_AllEdgesExactTriangle
-- name    : APSPExponentImprovement_AllEdgesExactTriangle
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T13:15:43.89892+00:00
-- url     : https://prove2.me/theorems/58c57275-f57b-4ffb-8886-d6f8424f6495
-- title:
--   All-edges Exact Triangle and exact output flags
-- statement:
--   An all-edges Exact Triangle instance consists of three integer weight matrices AB, BC, AC on n vertices per part, serialized row by row in that order. The output consists of three n-by-n row-major blocks of flags in the same order. Each flag is exactly one if the corresponding edge lies in a zero-sum triangle, and exactly zero otherwise. The problem always requires acceptance. The existing word-RAM semantics and running-time definition are reused without modification.
-- source:
--   https://arxiv.org/html/2610.06783v1#S6; conclusion footnote 10 and Section 3.2

import Definitions.Def_TrulySubcubicAPSP_Problems

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace APSPExponentImprovement

/-- A signed integer output is exactly the zero/one indicator of a proposition. -/
def IsFlag (v : Int) (p : Prop) : Prop :=
  (v = 1 ∧ p) ∨ (v = 0 ∧ ¬p)

/-- Three row-major weight matrices encode the AB, BC, and AC edges of a
complete tripartite graph. Output three row-major blocks of flags, in that
same order, marking every edge that belongs to a zero-weight triangle. -/
def AllEdgesExactTriangle : TrulySubcubicAPSP.Problem where
  Instance n := (Fin n → Fin n → Int) × (Fin n → Fin n → Int) ×
    (Fin n → Fin n → Int)
  input := fun (wAB, wBC, wAC) =>
    TrulySubcubicAPSP.rowByRow wAB ++ TrulySubcubicAPSP.rowByRow wBC ++
      TrulySubcubicAPSP.rowByRow wAC
  output := fun {n} (wAB, wBC, wAC) out =>
    (∀ a b : Fin n, IsFlag (out (a.val * n + b.val))
      (∃ c : Fin n, wAB a b + wBC b c + wAC a c = 0)) ∧
    (∀ b c : Fin n, IsFlag (out (n * n + b.val * n + c.val))
      (∃ a : Fin n, wAB a b + wBC b c + wAC a c = 0)) ∧
    (∀ a c : Fin n, IsFlag (out (2 * n * n + a.val * n + c.val))
      (∃ b : Fin n, wAB a b + wBC b c + wAC a c = 0))

end APSPExponentImprovement


