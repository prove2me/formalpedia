-- Prove2me | Definitions.Def_CompetitionComplexity_ODE
-- name    : CompetitionComplexity_ODE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:34.703609+00:00
-- url     : https://prove2.me/theorems/0d5e21ca-15ed-4e99-a11a-edd4a1ac0b59
-- title:
--   The differential equation (15)–(16), the function $M_\varepsilon$, and the third derivative $y'''$
-- statement:
--   Fix $\varepsilon>0$. The paper's differential equation is
--   $$
--   y'(t)=y(t)\bigl(\log y(t)-1\bigr)-\varepsilon\quad\text{for } t\in(0,\phi(\varepsilon)),\qquad y(0)=1, \tag{15–16}
--   $$
--   with $y(\phi(\varepsilon))=\lim_{t\uparrow\phi(\varepsilon)}y(t)$ the continuous extension. A **solution** is a function $y$ that
--
--   1. is continuous on $[0,\phi(\varepsilon)]$ with $y(0)=1$, and
--   2. at every $t\in(0,\phi(\varepsilon))$ satisfies $y(t)>0$ and is differentiable with $y'(t)=y(t)(\log y(t)-1)-\varepsilon$.
--
--   The paper also uses
--   $$
--   M_\varepsilon(x)=\Bigl(\log x-1-\frac{\varepsilon}{x}\Bigr)\bigl(x\log^2x+x\log x-x-\varepsilon\bigr),
--   $$
--   and the third derivative $y'''(t)$ of a solution on $[0,\phi(\varepsilon)]$, one-sided at $t=0$. Proposition 6 shows $y'''=M_\varepsilon\circ y$. The equation is the continuous counterpart of the recursion (9): its solution reaches $0$ exactly at time $\phi(\varepsilon)$.
--
--   **Formalization Note** Positivity of $y(t)$ is part of the solution notion because $\log$ in (15) is the real logarithm of a positive number; Lean's $\log y=\log|y|$ would otherwise admit spurious negative solutions. Values of $y$ outside $[0,\phi(\varepsilon)]$ are unconstrained and never used. $y'''$ is the iterated derivative within $[0,\phi(\varepsilon)]$; it is used only on $[0,\phi(\varepsilon))$, since at $\phi(\varepsilon)$ the solution is $0$ and $y'''$ involves $\varepsilon/y$.
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, §5, displays (15)–(16), p.21; M_ε, p.22; y‴ in Proposition 6, pp.22–23

import Mathlib
import Definitions.Def_CompetitionComplexity_Phi

namespace CompetitionComplexity

/-- **Solution of the differential equation (15)–(16).**
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), §5, p.21:
"y′(t) = y(t)(log(y(t)) − 1) − ε for every t ∈ (0, ϕ(ε)), (15) y(0) = 1. (16) We define
y(ϕ(ε)) = lim_{t↑ϕ(ε)} y(t) as the continuous extension of y in ϕ(ε)."

`IsSol ε y`: `y` is continuous on `[0, ϕ(ε)]`, `y(0) = 1`, and at every `t ∈ (0, ϕ(ε))` the
value `y(t)` is positive and `y` is differentiable with `y′(t) = y(t)(log y(t) − 1) − ε`.

**Formalization Note.** (1) Positivity of `y(t)` on `(0, ϕ(ε))` is part of the solution notion:
`log` in (15) is the real logarithm, defined only for positive arguments, whereas Lean's
`Real.log y = Real.log |y|` would admit spurious negative solutions. (2) Continuity on the closed
interval encodes (16) together with the continuous extension at `ϕ(ε)`. (3) Values of `y`
outside `[0, ϕ(ε)]` are unconstrained and never used. -/
def IsSol (ε : ℝ) (y : ℝ → ℝ) : Prop :=
  ContinuousOn y (Set.Icc 0 (phi ε)) ∧ y 0 = 1 ∧
    ∀ t ∈ Set.Ioo 0 (phi ε), 0 < y t ∧ HasDerivAt y (y t * (Real.log (y t) - 1) - ε) t

/-- **The function `Mε(x) = (log(x) − 1 − ε/x)(x log²(x) + x log(x) − x − ε)`**, §5, p.22.

**Formalization Note.** `log²(x)` is `(log x)²`. `Mε` is only evaluated at `x = yε(t) > 0`. -/
noncomputable def Meps (ε x : ℝ) : ℝ :=
  (Real.log x - 1 - ε / x) * (x * Real.log x ^ 2 + x * Real.log x - x - ε)

/-- **The third derivative `y‴(t)`** of a solution on `[0, ϕ(ε)]`, as used in Proposition 6
(p.22–23).

**Formalization Note.** Taken within `[0, ϕ(ε)]` (`iteratedDerivWithin`), so that at `t = 0` it
is the one-sided derivative the paper uses (`y` is not defined left of `0`); at interior points
it is the ordinary third derivative. At `t = ϕ(ε)`, where `y = 0` and `y‴` involves `ε/y`, it is
not used. -/
noncomputable def y3 (ε : ℝ) (y : ℝ → ℝ) (t : ℝ) : ℝ :=
  iteratedDerivWithin 3 y (Set.Icc 0 (phi ε)) t

end CompetitionComplexity


