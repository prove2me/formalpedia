-- Prove2me | Definitions.Def_Grothendieck_Fubini
-- name    : Grothendieck_Fubini
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T04:52:12.037448+00:00
-- url     : https://prove2.me/theorems/52bf1a03-53e2-4492-87da-84282b9b36c4
-- title:
--   The integrand and plane measure of the Fubini step of Lemma 2.1
-- statement:
--   The Fubini step of Lemma 2.1 exchanges the Gaussian integral over the random matrix $W$ with the two Laplace parameters $s,t>0$. This node fixes the two objects that step is stated with: the **signed integrand**
--
--   $$\mathrm{fubiniIntegrand}_r(W,(s,t))=\langle X,Y\rangle\,(st)^{-1/2}\exp\!\big(-(s\lVert X\rVert^2+t\lVert Y\rVert^2)\big),$$
--
--   where $X,Y$ are the two columns of $W$, and the **plane measure**, Lebesgue measure restricted to the open positive quadrant $(0,\infty)^2$, on which the parameters live.
--
--   The integrand is the product of the paper's numerator $\langle X,Y\rangle$ with the Laplace kernel $\frac1\pi\int\!\!\int (st)^{-1/2}e^{-(sA+tB)}$ taken at $A=\lVert X\rVert^2$, $B=\lVert Y\rVert^2$ — that is, the singular factor $1/(\lVert X\rVert\lVert Y\rVert)$ has already been absorbed into the parameters. Its absolute value is dominated by $\lVert X\rVert\lVert Y\rVert$ times the kernel, whose total mass in $(s,t)$ is $\pi$.
--
--   **Formalization Note** Both are plain definitions; they are separated from the theorem that uses them because platform statements cannot carry local definitions.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Lemma 2.1, pp. 84-87.

import Mathlib
import Definitions.Def_Grothendieck_Reduced

/-!
# The integrand and measure of the Fubini step of Lemma 2.1
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- The signed integrand of the Fubini step: the inner product of the two columns times the Laplace
kernel. -/
def fubiniIntegrand (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) (p : ℝ × ℝ) : ℝ :=
  inner ℝ (colFun r 0 W) (colFun r 1 W) *
    ((p.1 * p.2) ^ (-(1/2) : ℝ) *
      Real.exp (-(p.1 * ‖colFun r 0 W‖ ^ 2 + p.2 * ‖colFun r 1 W‖ ^ 2)))

/-- The product measure on the positive quadrant of the `(s,t)` plane. -/
def planeMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))

end Grothendieck


