-- Prove2me | Definitions.Def_Zeta5_SourceGrowthErrors
-- name    : Zeta5_SourceGrowthErrors
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-12T18:23:09.538813+00:00
-- url     : https://prove2.me/theorems/9b488d2d-4b8e-441a-b5d8-13e724a1c946
-- title:
--   The layer function and the additive errors of the inner per-prime bound (layer, Bmax, hIn, Ctab)
-- statement:
--   This module reproduces the auxiliary definitions of the inner per-prime bound of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0: the layer-cake function $T(t) = \sum_{j \le J} (t - jp/2)^+$ (`layer`, from `Apery/Growth/ClassData.lean`), the zero-class deficit bound `Bmax` and the class function `hIn` (from `Apery/Growth/InnerPrime.lean`), and the additive error `Ctab` of the continuous table bound (from `Apery/Growth/TablePrime.lean`). Nothing is proved here; the definitions are used by `Apery.inner_Lp_le`, `Apery.table_Lp_le` and `Apery.Ctab_le`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/ClassData.lean#L20-L24, Apery/Growth/InnerPrime.lean#L65-L80, Apery/Growth/TablePrime.lean#L24-L34

import Mathlib
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourceGrowthTables

/-!
# The layer function and the additive errors of the inner per-prime bound

* `layer p J t = ∑_{j ≤ J} (t - j p/2)⁺`, the layer-cake function controlling the factorial
  valuations (`Apery/Growth/ClassData.lean`);
* `Bmax`, the zero-class deficit bound, and `hIn`, the class function of the inner range
  (`Apery/Growth/InnerPrime.lean`);
* `Ctab`, the additive error of the continuous inner table bound
  (`Apery/Growth/TablePrime.lean`).

Nothing is proved in this module; the definitions are reproduced verbatim from the source.
-/

open Finset

namespace Apery

/-- The layer-cake function `T(t) = ∑_{j ≤ J} (t - j p/2)⁺`. -/
noncomputable def layer (p J : ℕ) (t : ℝ) : ℝ := ∑ j ∈ Icc 1 J, max 0 (t - j * p / 2)

/-- The zero-class deficit bound. -/
noncomputable def Bmax (n p : ℕ) : ℝ :=
  max 0 ((ktopI n p : ℝ) / 2 - ((5 + 12 * ((3 * n / p : ℕ) : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ)) - 4) / 2) *
    (max 0 ((ktopI n p : ℝ) / 2 - ((5 + 12 * ((3 * n / p : ℕ) : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ)) - 4) / 2) / 2 + 1)

/-- The class function of the inner range. -/
noncomputable def hIn (n p : ℕ) (k : ℤ) (a a' : ℕ) : ℝ :=
  (psiR k (12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4 + 6 * (a' : ℤ) - a) : ℝ)

/-- The additive error of the table bound. -/
noncomputable def Ctab (n p : ℕ) (k : ℤ) : ℝ :=
  5 * ∑ i, ∑ j, |bIn (40 * n / p) (3 * n / p) k i j| +
    ((ktopI n p - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) + 2 * Bmax n p + 1

end Apery


