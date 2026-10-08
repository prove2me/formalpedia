-- Prove2me | Definitions.Def_MazurTransfer_Order49MarkedOriginPoint
-- name    : MazurTransfer_Order49MarkedOriginPoint
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T03:42:08.359165+00:00
-- url     : https://prove2.me/theorems/7debaf64-5b3e-4a3e-bade-f44bc9c71e94
-- title:
--   Exact marked origin point of the rational order-seven family
-- statement:
--   For each rational parameter d for which the prescribed order-seven source curve is elliptic, the marked group point is the original nonsingular affine point (0,0). This exact proof-bearing constructor uses only its separately Proved nonsingularity theorem.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Apache-2.0 headers and attribution retained. Exact original kernel graph and Lean AST declaration ranges. All constructor values are compared against their WIP originals by kernel-checked reflexivity and proof irrelevance using standard axioms. The nonsingularity prerequisite are independently Proved platform targets and locally rechecked closed proofs. Named downstream consumers: original residual modular relation and residual Hauptmodul specification, then the full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenOrigin_nonsingular

theorem MazurTorsion.Kubert.orderSevenOrigin_nonsingular (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular 0 0 := by
  exact MazurTransfer.order49_point_map_orderSevenOrigin_nonsingular d


/- Source module: MazurTorsion.Kubert.OrderSevenIsogeny. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert












































































/-- The marked order-seven point `(0,0)` on the source family. -/
@[expose] public noncomputable def orderSevenOrigin
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point :=
  .some 0 0 (MazurTorsion.Kubert.orderSevenOrigin_nonsingular d)























































end MazurTorsion.Kubert

end

#print axioms MazurTorsion.Kubert.orderSevenOrigin


