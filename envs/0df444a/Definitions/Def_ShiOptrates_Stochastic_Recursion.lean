-- Prove2me | Definitions.Def_ShiOptrates_Stochastic_Recursion
-- name    : ShiOptrates_Stochastic_Recursion
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-08T22:24:11.397876+00:00
-- url     : https://prove2.me/theorems/d0d5bad5-dda1-4712-8c17-7e8b2eee419e
-- title:
--   $\mathrm{ExpectedDescent}$: the one-step recursion abstracting a stochastic method
-- statement:
--   The abstract one-step inequality that every stochastic rate in the library is derived from.
--
--   For sequences $a_k$ (objective gap) and $b_k$ (squared gradient norm), a stepsize $h$, a smoothness constant $L$ and a variance proxy $\sigma$, $\mathrm{ExpectedDescent}$ asserts
--   $$a_{k+1}\;\le\;a_k-\tfrac{h}{2}\,b_k+\tfrac{L h^{2}\sigma^{2}}{2}.$$
--
--   Isolating this recursion is what lets one accumulation argument serve SGD, the variance-purchase schedule, and the SPIDER epochs: each supplies the inequality by a different route and inherits the same telescoping conclusion.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/Recursion.lean | Formalized by Yueheng Shi; Apache License 2.0. Platform copy produced by declaration-graph skeleton subtraction; root namespace `OptRates` renamed to `ShiOptRates`.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/Recursion.lean
Original work Copyright (c) 2026 Yueheng Shi, released under the Apache License,
Version 2.0.  The original copyright and author notices are retained below.

MODIFICATIONS made for publication on Prove2me: declarations not reachable from
the published targets were removed by declaration-graph skeleton subtraction;
project imports were rewritten to platform `Definitions.Def_*` / `Theorems.Thm_*`
modules; the root namespace `OptRates` was renamed to `ShiOptRates`; 
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiOptrates_Cost
import Definitions.Def_ShiOptrates_FunctionClass
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# L3a — The expected-descent recursion

The part of the classical SGD analysis that is *not* probabilistic.  Every
expectation-based rate proof for a first-order method passes through a scalar recursion of
the form

`aₖ₊₁ ≤ aₖ - (h/2) bₖ + L h² σ² / 2`

where `aₖ = E f(xₖ)` and `bₖ = E‖∇f(xₖ)‖²`.  Establishing that recursion is the
probabilistic step (`Optrates.Stochastic.OneStep`); turning it into a rate is real
analysis, and is done here once.

Separating the two is what makes the `ε⁻⁴` bound auditable: the constant `8 L Δ₀ σ² / ε⁴`
below is a consequence of arithmetic on the recursion alone, and no martingale theory can
change it.

## Main results

* `sum_le_of_expectedDescent` — telescoping the recursion.
* `exists_le_of_expectedDescent` — `min_{k<K} bₖ ≤ 2Δ₀/(hK) + L h σ²`, the standard
  two-term bound with both terms explicit.
* `exists_le_sq_of_stepsize` — **GL3's arithmetic core**: at `h = ε²/(2Lσ²)` and
  `K ≥ 8 L Δ₀ σ² / ε⁴` some `bₖ ≤ ε²`.  Stepsize supplied and verified, not derived, per
  the library's convention.
-/

namespace ShiOptRates.Stochastic

open Finset

variable {a b : ℕ → ℝ} {h L σ : ℝ} {K : ℕ}

/-- The recursion satisfied by `(E f(xₖ), E‖∇f(xₖ)‖²)` along SGD with stepsize `h` on an
`L`-smooth objective with gradient-noise second moment `σ²`.

Stated as a predicate on two real sequences so that the rate below is independent of how
the recursion was obtained — from a martingale argument, from a concentration argument, or
from a hypothesis. -/
def ExpectedDescent (a b : ℕ → ℝ) (h L σ : ℝ) (K : ℕ) : Prop :=
  ∀ k < K, a (k + 1) ≤ a k - h / 2 * b k + L * h ^ 2 * σ ^ 2 / 2

end ShiOptRates.Stochastic


