-- Prove2me | Definitions.Def_ZetaNine_CoefficientMap
-- name    : ZetaNine_CoefficientMap
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-03T15:28:10.468499+00:00
-- url     : https://prove2.me/theorems/8aaaa1e7-befc-4a25-a4f5-26c37740eb40
-- title:
--   Actual rational function and cleared highest-pole coefficient
-- statement:
--   Let $n,j$ be natural numbers and let $t$ be rational. The actual numerator and pole product are
--
--   $$N_n(t)=n!^7\prod_{i=1}^{n}(t-i)\prod_{i=1}^{n}(t+n+i),\qquad Q_n(t)=\prod_{k=0}^{n}(t+k),\qquad R_n(t)=\frac{N_n(t)}{Q_n(t)^9}.$$
--
--   Let $Q_{n,j}(t)$ be the product over $0\le k\le n$ with $k\ne j$, and set $\widetilde R_{n,j}(t)=N_n(t)/Q_{n,j}(t)^9$ and $C_{n,j}=\widetilde R_{n,j}(-j)$. For a rational polynomial $W$, the actual weighted function is $R_n(t)W(t(t+n))$; its cleared expression and highest cleared-pole value are defined by multiplying $\widetilde R_{n,j}$ by the same polynomial evaluation and then evaluating at $t=-j$.
--
--   These finite-product constructions provide the interface for clearing a pole and computing the actual highest coefficient. No binomial coefficient closed formula is used as a definition. The unmodified rational division operations are total; a pole coefficient uses the cleared expression, not $R_n(-j)$.
-- source:
--   Zeta(9) research notes: missions/zeta9/research/coefficient-map-finite-entry-2026-10-03.md (actual product definitions and highest cleared-pole coefficient); underlying missions/zeta9/round5/research/arithmetic.md, equations (1), (5), and (6), specialized to p=9, one layer q=1, m=n. Frozen verified Lean source missions/zeta9/formalization/CoefficientMap.lean, SHA256 e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03. Definition declarations are the exact original Lean parser spans.

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factorial.BigOperators

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMap

def numerator (n : ℕ) (t : ℚ) : ℚ :=
  (n.factorial : ℚ) ^ 7 *
    (∏ i ∈ range n, (t - ((i : ℚ) + 1))) *
    (∏ i ∈ range n, (t + n + ((i : ℚ) + 1)))

def poleProduct (n : ℕ) (t : ℚ) : ℚ :=
  ∏ k ∈ range (n + 1), (t + k)

def actualR (n : ℕ) (t : ℚ) : ℚ := numerator n t / poleProduct n t ^ 9

def clearedPoleProduct (n j : ℕ) (t : ℚ) : ℚ :=
  ∏ k ∈ (range (n + 1)).erase j, (t + k)

def clearedR (n j : ℕ) (t : ℚ) : ℚ :=
  numerator n t / clearedPoleProduct n j t ^ 9

def leadingPoleCoefficient (n j : ℕ) : ℚ := clearedR n j (-(j : ℚ))

def weightedR (n : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ :=
  actualR n t * W.eval (t * (t + n))

def clearedWeightedR (n j : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ :=
  clearedR n j t * W.eval (t * (t + n))

def weightedLeadingPoleCoefficient (n j : ℕ) (W : ℚ[X]) : ℚ :=
  clearedWeightedR n j W (-(j : ℚ))

end ZetaNine.CoefficientMap


