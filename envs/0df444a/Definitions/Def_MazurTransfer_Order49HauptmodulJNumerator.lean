-- Prove2me | Definitions.Def_MazurTransfer_Order49HauptmodulJNumerator
-- name    : MazurTransfer_Order49HauptmodulJNumerator
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T05:15:51.119114+00:00
-- url     : https://prove2.me/theorems/b7b768a1-9a7a-4a7f-9581-1428a0549a90
-- title:
--   Exact original Hauptmodul j numerator
-- statement:
--   Exact original Hauptmodul j numerator and four selection/division cofactor polynomials with every value independently kernel-reflexivity audited; no resultant nonvanishing proof or other mathematical theorem is bundled as data
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; Apache-2.0 headers and attribution retained. One exact pure definition selected by original kernel type dependencies and complete original Lean AST source ranges. Every exported value is compared against the original using standard axioms. Existing exact published selection and cofactor data are reused. Named downstream consumers: original residual Hauptmodul specification and the full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors


/- Source module: MazurTorsion.Kubert.OrderSevenCorrespondence. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
namespace MazurTorsion.Kubert

/-- The numerator in the level-seven Hauptmodul formula
`j(t) = J₇(t) / t⁷`. -/
def orderSevenJNumerator (t : ℚ) : ℚ :=
  (t ^ 2 + 13 * t + 49) * (t ^ 2 + 245 * t + 2401) ^ 3

















end MazurTorsion.Kubert

end
end

#print axioms MazurTorsion.Kubert.orderSevenJNumerator


