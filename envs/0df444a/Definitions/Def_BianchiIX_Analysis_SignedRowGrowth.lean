-- Prove2me | Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
-- name    : BianchiIX_Analysis_SignedRowGrowth
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T00:30:53.916499+00:00
-- url     : https://prove2.me/theorems/e7a96cf0-8c8d-41f7-8c1b-cdb924eacd12
-- title:
--   Signed row sums for supremum-norm comparison
-- statement:
--   For a finite index type $\iota$, a real matrix $A=(A_{ij})$, and $i\in\iota$,
--   define its signed row sum by
--   $$\sigma_i(A)=A_{ii}+\sum_{j\ne i}|A_{ij}|.$$
--   Vectors in $\mathbb R^\iota$ carry the supremum norm.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/SignedRowGrowth.lean

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The diagonal keeps its sign in the logarithmic bound for the supremum norm. -/
def signedRowSum (A : Matrix ι ι ℝ) (i : ι) : ℝ :=
  A i i + ∑ j ∈ Finset.univ.erase i, |A i j|











end BianchiIX


