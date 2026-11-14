-- Prove2me | Definitions.Def_NarrowDNF_ShiftProbability
-- name    : NarrowDNF_ShiftProbability
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T08:01:02.944686+00:00
-- url     : https://prove2.me/theorems/fa09d29b-27df-4ec0-872d-a09a39ca6aa1
-- title:
--   Applying a coordinate-shift order using a Boolean choice assignment
-- statement:
--   Let $v:\{0,1\}^{\iota}\to\{0,1\}$, let $\mathcal O$ be an ordered list of coordinates, and let $d\in\{0,1\}^{\iota}$ specify the shift choice at each coordinate. Define the shifted function by applying, in list order, the upper shift at an occurrence of $i$ when $d_i=0$ and the lower shift when $d_i=1$. The upper shift has slices $(v_0,v_0\lor v_1)$; the lower shift has slices $(v_0\land v_1,v_1)$.
--
--   The order is retained explicitly. Repeated coordinates are allowed by the construction, and every occurrence of the same coordinate uses the same bit $d_i$. For a list without repetitions and a Bernoulli-$p$ choice assignment, the coordinate choices are independent, with lower-shift probability $p$ and upper-shift probability $1-p$. This definition is the deterministic function of the choice cube used in the subsequent randomized error analysis. It does not itself assert an error inequality or any commutation property of shifts.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ShiftProbability.lean#L96-L99

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_CoordinateShift

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

namespace NarrowDNF.ShiftProbability
end NarrowDNF.ShiftProbability


/-!
# Randomized coordinate shifting under the biased product measure

This file proves the full error inequality of Lemma 3.1 and the iterated
expectation inequality following Lemma 3.1 in the 2026-11-06 STOC revision. Random choices form an
explicit Bernoulli product cube; the independence needed by iteration is
derived from the finite-sum Fubini formula.
-/

noncomputable section

namespace NarrowDNF.ShiftProbability

open ProductMeasure

variable {ι : Type*} [DecidableEq ι]







variable [Fintype ι]









/-- Apply a fixed coordinate order, using the corresponding bits of `d`
as the lower/upper choices. -/
def shiftByChoices (order : List ι) (d : Cube ι) (v : Cube ι → Bool) : Cube ι → Bool :=
  applyShifts (order.map fun i => (i, d i)) v



















end NarrowDNF.ShiftProbability


