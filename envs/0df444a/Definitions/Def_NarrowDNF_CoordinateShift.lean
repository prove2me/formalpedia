-- Prove2me | Definitions.Def_NarrowDNF_CoordinateShift
-- name    : NarrowDNF_CoordinateShift
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:31.027352+00:00
-- url     : https://prove2.me/theorems/d7496803-53f8-434c-ae00-22d28f13f4f9
-- title:
--   Upper and lower coordinate shifts and their ordered iteration
-- statement:
--   For $x\in\{0,1\}^I$, write $x^{i\leftarrow0}$ and $x^{i\leftarrow1}$ for the inputs obtained by fixing coordinate $i$. For any Boolean function $v$, define
--   $$U_i v(x)=v(x)\lor v(x^{i\leftarrow0}),\qquad
--   L_i v(x)=v(x)\land v(x^{i\leftarrow1}).$$
--   Equivalently, the two slices become $(v_0,v_0\lor v_1)$ and $(v_0\land v_1,v_1)$, respectively. The formulas are meaningful for arbitrary $v$, without an initial monotonicity assumption.
--
--   The predicate of monotonicity in coordinate $i$ is $v(x^{i\leftarrow0})\le v(x^{i\leftarrow1})$ for every $x$, with all other coordinates fixed. A Boolean choice selects the lower shift when true and the upper shift when false. A finite list of such choices is applied in list order, retaining repetitions and making no commutativity assumption. These are the concrete operations whose order-preservation and bias-matched error properties are established by separate theorem nodes.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/CoordinateShift.lean#L57-L59
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/CoordinateShift.lean#L97-L99
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/CoordinateShift.lean#L101-L104
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/CoordinateShift.lean#L17-L17
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/CoordinateShift.lean#L19-L19
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/CoordinateShift.lean#L21-L22
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/CoordinateShift.lean#L24-L25

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive

namespace NarrowDNF
end NarrowDNF


/-!
# Coordinate shifts on Boolean functions

The unbranched shift formulas are equivalent to the two-slice definitions in
the shift definitions preceding Lemma 3.1 of the 2026-11-06 STOC revision, by Boolean idempotence. This file concerns
monotonicity; the global biased-error bound requires a separate finite-sum
argument.
-/

namespace NarrowDNF

variable {ι : Type*} [DecidableEq ι]

def lowerInput (i : ι) (x : Cube ι) : Cube ι := Function.update x i false

def upperInput (i : ι) (x : Cube ι) : Cube ι := Function.update x i true

def upperShift (i : ι) (v : Cube ι → Bool) (x : Cube ι) : Bool :=
  v x || v (lowerInput i x)

def lowerShift (i : ι) (v : Cube ι → Bool) (x : Cube ι) : Bool :=
  v x && v (upperInput i x)













/-- Nondecreasing in one coordinate, with the other coordinates held fixed. -/
def CoordinateMonotone (i : ι) (v : Cube ι → Bool) : Prop :=
  ∀ x, v (lowerInput i x) ≤ v (upperInput i x)









/-- A Boolean records whether the lower shift was chosen. -/
def shiftChoice (i : ι) (useLower : Bool) (v : Cube ι → Bool) : Cube ι → Bool :=
  if useLower then lowerShift i v else upperShift i v

/-- Apply shifts in list order; no commutativity of shifts is assumed. -/
def applyShifts : List (ι × Bool) → (Cube ι → Bool) → (Cube ι → Bool)
  | [], v => v
  | (i, b) :: rest, v => applyShifts rest (shiftChoice i b v)



















end NarrowDNF


