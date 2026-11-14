-- Prove2me | Definitions.Def_NarrowDNF_WidthBound
-- name    : NarrowDNF_WidthBound
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:12.641867+00:00
-- url     : https://prove2.me/theorems/ce33f545-a1ac-4dd5-aa51-a8156a7fd47f
-- title:
--   Explicit degree, load, and width budgets for the final approximation
-- statement:
--   For a real influence bound $K$ and error tolerance $\varepsilon$, let $c(K)=\lceil K\rceil_{\mathbb N}$ be the nonnegative-integer ceiling. The final arithmetic budgets are
--   $$d(K,\varepsilon)=\left\lceil\frac{4000c(K)}\varepsilon\right\rceil_{\mathbb N},\qquad L(K,\varepsilon)=\exp\!\left(\frac{160000000000\,c(K)^2}{\varepsilon^2}\right),$$
--   $$w(K,\varepsilon)=\left\lceil\frac{4\,2^{d(K,\varepsilon)}L(K,\varepsilon)}\varepsilon\right\rceil_{\mathbb N}.$$
--   The explicit absolute constant is $C=10000000000000=10^{13}$, independent of dimension and bias.
--
--   These functions are the numerical choices used to combine the activation arity and load bounds, the monotonicization error budget, and certificate truncation. Their intended theorem range is $K>0$ and $0<\varepsilon<1$; the subsequent arithmetic lemmas state the precise hypotheses needed to compare $w(K,\varepsilon)$ with $\exp(C(K+1)^2/\varepsilon^2)$. Defining the budgets does not assume or prove the structural existence of the activation family or DNF approximator.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/WidthBound.lean#L21-L21
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/WidthBound.lean#L23-L23
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/WidthBound.lean#L25-L26
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/WidthBound.lean#L28-L28
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/WidthBound.lean#L30-L31

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace NarrowDNF.WidthBound
end NarrowDNF.WidthBound


/-!
# Explicit width and error-budget arithmetic

These are the final arithmetic estimates in the proof of Theorem 1.2 of
the 2026-11-06 STOC revision. The source's numerical constants are retained. This
module does not assume or assert the structural theorem supplying the
approximator and activation family.
-/

noncomputable section

namespace NarrowDNF.WidthBound

def influenceCeil (K : ℝ) : ℕ := Nat.ceil K

def degree (K ε : ℝ) : ℕ := Nat.ceil (4000 * (influenceCeil K : ℝ) / ε)

def loadBound (K ε : ℝ) : ℝ :=
  Real.exp (160000000000 * (influenceCeil K : ℝ)^2 / ε^2)

def width (K ε : ℝ) : ℕ := Nat.ceil (4 * (2 : ℝ)^(degree K ε) * loadBound K ε / ε)

/-- One explicit absolute constant; no dependence on dimension or bias. -/
def absoluteConstant : ℝ := 10000000000000

















end NarrowDNF.WidthBound


