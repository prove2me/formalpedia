-- Prove2me | Definitions.Def_PeskirShiryaev_SharpInequalities_logarithmicCosts
-- name    : PeskirShiryaev_SharpInequalities_logarithmicCosts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:25:16.503326+00:00
-- url     : https://prove2.me/theorems/dfd4bd35-8996-4080-87f2-ee594e4a50e4
-- title:
--   Logarithmic costs, exact constants, and extended expectations
-- statement:
--   For $y\ge0$, let $G_{\log}(y)=y\log y$, with $G_{\log}(0)=0$, and $G_+(y)=y\max(\log y,0)$. For $c>1$ and $x\ge0$, the constants in the maximal inequalities are as follows.
--
--   Write $\alpha=(c-1)/c$, $v_*=c/[e(c-1)]$, $u_*=1+1/[e^c(c-1)]$, and $s_*=c/(c-1)$. The constants are
--   $$
--   W_{\log}(x;c)=\begin{cases}c^2/[e(c-1)]&0\le x\le v_*,\\cx\log\!\frac{c}{x(c-1)}&x>v_*,\end{cases}
--   $$
--   and
--   $$
--   W_+(x;c)=\begin{cases}u_*&0\le x\le u_*,\\x+(1-x)\log(x-1)-(c+\log(c-1))(x-1)&u_*<x\le s_*,\\cx\log\!\frac{c}{x(c-1)}&x>s_* .\end{cases}
--   $$
--   Adjacent branches agree at their endpoints.
--
--   For a nonnegative random variable $Y$ on a probability space, define its extended cost expectation by
--   $$\mathcal E_G(Y)=\int (G(Y)+1/e)\,dP-1/e.$$
--   The integral is nonnegative and may be infinite; both costs are bounded below by $-1/e$. These definitions keep the two costs and all their exact constants together for the Brownian and submartingale statements.
--
--   **Formalization Note** The subtraction is in the extended reals and subtracts only a finite constant. The total real logarithm gives $0\log0=0$. The formulas are used only for nonnegative arguments and $c>1$. The explicit bound is not a definition of an optimal stopping value.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 274, 278–282 (PDF pp. 292, 296–300), Eqs. (19.2.1), (19.2.2), (19.2.28)–(19.2.30), (19.2.45), (19.2.46)

import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Data.EReal.Basic
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

namespace PeskirShiryaev.SharpInequalities

/-- The two costs of Section 19.2. -/
inductive LogCost where
  | plain
  | plus
  deriving DecidableEq

/-- At zero both costs equal zero, including the continuous extension of y log y. -/
def logarithmicCost (k : LogCost) (y : ℝ) : ℝ :=
  match k with
  | .plain => y * Real.log y
  | .plus => y * max (Real.log y) 0

def alpha (c : ℝ) : ℝ := (c - 1) / c

def vStar (c : ℝ) : ℝ := c / (Real.exp 1 * (c - 1))

def uStar (c : ℝ) : ℝ := 1 + 1 / (Real.exp c * (c - 1))

def sStar (c : ℝ) : ℝ := c / (c - 1)

/-- The explicit right-hand-side constant, not a definition of the stopping value.
The adjacent formulas agree at vStar, uStar and sStar when c > 1. -/
def boundConstant (k : LogCost) (x c : ℝ) : ℝ :=
  match k with
  | .plain => if x ≤ vStar c then c ^ 2 / (Real.exp 1 * (c - 1))
      else c * x * Real.log (c / (x * (c - 1)))
  | .plus => if x ≤ uStar c then uStar c
      else if x ≤ sStar c then
        x + (1 - x) * Real.log (x - 1) - (c + Real.log (c - 1)) * (x - 1)
      else c * x * Real.log (c / (x * (c - 1)))

/-- Extended expectation of a logarithmic cost on a nonnegative random variable.
Both costs are bounded below by -1/e; adding 1/e, integrating nonnegatively, and
subtracting 1/e preserves finite negative expectations and positive infinity. -/
def costExpectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (k : LogCost) (Y : Ω → ℝ) : EReal :=
  ((∫⁻ ω, ENNReal.ofReal (logarithmicCost k (Y ω) + 1 / Real.exp 1) ∂P) : EReal)
    - ((1 / Real.exp 1 : ℝ) : EReal)

end PeskirShiryaev.SharpInequalities


