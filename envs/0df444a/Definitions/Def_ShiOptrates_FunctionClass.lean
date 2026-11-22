-- Prove2me | Definitions.Def_ShiOptrates_FunctionClass
-- name    : ShiOptrates_FunctionClass
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-08T22:23:54.386961+00:00
-- url     : https://prove2.me/theorems/e2772808-aca8-4d4c-bdac-a5cffa14426e
-- title:
--   Function classes: the quadratic upper bound $\mathrm{QuadUpper}$ and the Polyak--\L{}ojasiewicz condition
-- statement:
--   The analytic assumptions under which convergence rates are stated, as predicates on an explicitly supplied gradient map rather than as a bundled structure.
--
--   Let $E$ be a real inner-product space, $f:E\to\mathbb{R}$ an objective and $g:E\to E$ a map playing the role of its gradient. Then $\mathrm{QuadUpper}\,f\,g\,L$ asserts the descent-lemma inequality
--   $$f(y)\;\le\;f(x)+\langle g(x),\,y-x\rangle+\tfrac{L}{2}\|y-x\|^{2}\qquad\text{for all }x,y,$$
--   which is the form of $L$-smoothness that rate proofs actually consume. And $\mathrm{PolyakLojasiewicz}\,f\,g\,\mu\,f^{\star}$ asserts
--   $$2\mu\,(f(x)-f^{\star})\;\le\;\|g(x)\|^{2}\qquad\text{for all }x.$$
--
--   Stating smoothness as $\mathrm{QuadUpper}$ rather than as gradient-Lipschitzness is deliberate: it is exactly what every rate proof uses, it is provable by algebra for quadratic witnesses, and it is implied by a Lipschitz gradient. Because $g$ is a parameter, one rate theorem instantiates at an exact gradient, an inexact oracle, or a quantum estimator without editing the statement.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/FunctionClass.lean | Formalized by Yueheng Shi; Apache License 2.0. Platform copy produced by declaration-graph skeleton subtraction; root namespace `OptRates` renamed to `ShiOptRates`.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/FunctionClass.lean
Original work Copyright (c) 2026 Yueheng Shi, released under the Apache License,
Version 2.0.  The original copyright and author notices are retained below.

MODIFICATIONS made for publication on Prove2me: declarations not reachable from
the published targets were removed by declaration-graph skeleton subtraction;
project imports were rewritten to platform `Definitions.Def_*` / `Theorems.Thm_*`
modules; the root namespace `OptRates` was renamed to `ShiOptRates`; 
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# L0 — Function classes

Predicates naming the analytic assumptions that convergence-rate theorems are stated
under.  Everything is a plain `Prop` on an explicitly supplied gradient map `g`, rather
than a bundled structure: rate theorems in `Optrates.Deterministic` quantify over
`f`, `g`, `L`, and a proof of `QuadUpper f g L`, so that instantiating a rate at a new
function class is supplying a term, not editing a theorem.

The *defining* smoothness assumption in this library is `QuadUpper` (the descent-lemma
inequality), not gradient-Lipschitzness.  This is deliberate: `QuadUpper` is exactly what
every rate proof consumes, it is provable by algebra for quadratic witnesses, and it is
implied by gradient-Lipschitzness (`quadUpper_of_lipschitz_gradient`), which is the only
genuinely analytic lemma in the library.

## Main definitions

* `QuadUpper f g L` — `f y ≤ f x + ⟪g x, y - x⟫ + (L/2)‖y - x‖²`.  `L`-smoothness as used.
* `QuadLower f g μ` — `μ`-strong convexity in gradient form (`μ = 0`: convexity).
* `PolyakLojasiewicz f g μ f⋆` — `2μ(f x - f⋆) ≤ ‖g x‖²`.
* `BoundedBelow f f⋆` — `f⋆` is a lower bound for `f`.
* `LipschitzGradient g L` — `‖g x - g y‖ ≤ L‖x - y‖`.

## Main results

* `quadUpper_of_lipschitz_gradient` — the descent lemma: a Lipschitz gradient gives
  `QuadUpper` with the same constant.
-/

namespace ShiOptRates

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `L`-smoothness in the form every rate proof actually uses: the quadratic upper
bound (descent lemma inequality) `f y ≤ f x + ⟪g x, y - x⟫ + (L/2)‖y - x‖²`. -/
def QuadUpper (f : E → ℝ) (g : E → E) (L : ℝ) : Prop :=
  ∀ x y, f y ≤ f x + ⟪g x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2

/-- The Polyak–Łojasiewicz condition with modulus `mu` about the value `fstar`:
`2 mu (f x - fstar) ≤ ‖g x‖²`.  Not in Mathlib. -/
def PolyakLojasiewicz (f : E → ℝ) (g : E → E) (mu fstar : ℝ) : Prop :=
  ∀ x, 2 * mu * (f x - fstar) ≤ ‖g x‖ ^ 2

section Gradient

variable [CompleteSpace E]

variable {f : E → ℝ} {g : E → E} {L : ℝ}

end Gradient

end ShiOptRates


