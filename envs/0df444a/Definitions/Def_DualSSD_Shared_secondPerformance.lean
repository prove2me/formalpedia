-- Prove2me | Definitions.Def_DualSSD_Shared_secondPerformance
-- name    : DualSSD_Shared_secondPerformance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:33:58.562005+00:00
-- url     : https://prove2.me/theorems/e9cf8fd7-d7e1-415e-bd34-92c6b901e0e5
-- title:
--   Distribution function $F_X$, second performance function $F_X^{(2)}$ (2.1) and SSD (2.2)
-- statement:
--   Let $(\Omega,\mathcal B,\mathbb P)$ be a probability space and $X:\Omega\to\mathbb R$ a real random variable. Its **distribution function** (first performance function) is the right-continuous function
--   $$F_X(\eta)=\mathbb P\{X\le\eta\},\qquad \eta\in\mathbb R.$$
--   The **second performance function** is the area below the distribution function,
--   $$F_X^{(2)}(\eta)=\int_{-\infty}^{\eta}F_X(\xi)\,d\xi,\qquad \eta\in\mathbb R. \tag{2.1}$$
--   For two random variables $X,Y$ on the same space, $X$ **dominates $Y$ in the weak second-degree stochastic dominance** relation, written $X\succeq_{SSD}Y$, when
--   $$F_X^{(2)}(\eta)\le F_Y^{(2)}(\eta)\qquad\text{for all }\eta\in\mathbb R. \tag{2.2}$$
--   Larger outcomes are preferred, so the dominating variable has the smaller curve $F^{(2)}$.
--
--   These are the primal objects of the paper. They serve chunk 01-dual-characterization (p. 61, $F_X$; p. 62, (2.1)–(2.2); used by eq. (2.4) and the properties of $F^{(2)}_X$ on p. 62, the $p$-quantile characterization and the quantile function $F^{(-1)}_X$ on p. 64, (3.3) and Theorem 3.1 on p. 65, and Theorem 3.2 on p. 66, the SSD relation being the order that the dual characterization describes) and chunk 02-gini-efficiency (p. 61, $F_X$; p. 62, (2.1)–(2.3) and SSD-efficiency; used by the quantile function on pp. 64–65, the SSD-consistency results for the mean and the Gini mean difference, and Theorem 5.3 on p. 73).
--
--   **Formalization Note** $F_X(\eta)$ is `P.real {ω | X ω ≤ η}` and $F_X^{(2)}(\eta)$ is the Lebesgue (Bochner) integral of $F_X$ over $(-\infty,\eta]$. The integral is finite when $\mathbb E|X|<\infty$; every theorem that uses $F_X^{(2)}$ assumes `Integrable X P`, since a Bochner integral of a non-integrable function would be $0$.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 61 (definition of F_X) and p. 62, eqs. (2.1), (2.2)

import Mathlib

namespace DualSSD.Shared

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The (right-continuous) cumulative distribution function `F_X(η) = P{X ≤ η}` of a real random
variable `X` on the probability space `(Ω, P)` (Ogryczak–Ruszczyński 2002, §2, p. 61). -/
noncomputable def distFun (P : Measure Ω) (X : Ω → ℝ) (η : ℝ) : ℝ :=
  P.real {ω | X ω ≤ η}

/-- The second performance function (2.1), `F_X^(2)(η) = ∫_{−∞}^η F_X(ξ) dξ`
(Ogryczak–Ruszczyński 2002, §2, p. 62): the area below the distribution function up to `η`,
a Lebesgue (Bochner) integral over `(−∞, η]`. It is finite whenever `E|X| < ∞`; the theorems
that use it all assume `Integrable X P`. -/
noncomputable def secondPerformance (P : Measure Ω) (X : Ω → ℝ) (η : ℝ) : ℝ :=
  ∫ ξ in Set.Iic η, distFun P X ξ

/-- The weak second-degree stochastic dominance relation (2.2) (Ogryczak–Ruszczyński 2002, §2,
p. 62): `X ⪰_SSD Y` iff `F_X^(2)(η) ≤ F_Y^(2)(η)` for all `η ∈ ℝ` (larger outcomes preferred). -/
def SSD (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∀ η : ℝ, secondPerformance P X η ≤ secondPerformance P Y η

end DualSSD.Shared


