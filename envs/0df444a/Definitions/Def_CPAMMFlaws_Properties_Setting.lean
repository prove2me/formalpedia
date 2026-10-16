-- Prove2me | Definitions.Def_CPAMMFlaws_Properties_Setting
-- name    : CPAMMFlaws_Properties_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:46.287343+00:00
-- url     : https://prove2.me/theorems/e55a8eb5-af48-4210-bfbb-56ad8771cfa5
-- title:
--   §II.C, (3), p. 15 — the constant product market maker cost function p^cmm(x, X, Y) = xY/(X − x), and the linear market maker cost p^tmm
-- statement:
--   A **constant product automated market maker** (CPAMM) is a pool, held in a smart contract, containing $X$ units of a token $A$ and $Y$ units of a token $B$ deposited by liquidity providers. A trader who takes $x$ units of $A$ out of the pool (a buy if $x>0$, a sale of $-x$ units if $x<0$) pays the amount $y$ of $B$ that keeps the product of the reserves constant, $(X-x)(Y+y)=XY$. Equation (3) of the paper names the solution:
--
--   $$
--   p^{\mathrm{cmm}}(x, X, Y) \;:=\; x\cdot\frac{Y}{X-x}.
--   $$
--
--   A negative value is a revenue: selling $q>0$ units of $A$ into a pool $(X',Y')$ earns $-p^{\mathrm{cmm}}(-q, X', Y')$ units of $B$. After a buy of $x$ the pool holds $X-x$ units of $A$ and $Y+p^{\mathrm{cmm}}(x,X,Y)$ units of $B$.
--
--   For the comparison of Proposition 1 the file also defines the cost of the paper's linear ("traditional") market maker. When $N$ market makers with combined inventory $I$ quote the marginal price $V+\frac{\ell}{N}(t-I)$, with fundamental value $V$ and liquidity factor $\ell$, buying $x$ units costs
--
--   $$
--   p^{\mathrm{tmm}}(x, I) \;:=\; \int_0^x V+\frac{\ell}{N}(t-I)\,dt \;=\; x\Bigl(V-\frac{\ell}{N}I\Bigr)+\frac{\ell}{2N}x^2 .
--   $$
--
--   These two cost functions are the objects every statement of the mission is about.
--
--   **Formalization Note** `pcmm x X Y` is the closed form (3) on all of $\mathbb R^3$; Lean's convention $a/0=0$ makes it $0$ at $x=X$, so every theorem carries $x<X$ (or a stronger bound). The invariant characterization is Lemma 2, a separate theorem, not the definition. `ptmm x V ℓ N I` is the printed closed form of the integral, argument order $(x, V, \ell, N, I)$.
-- source:
--   Park, The Conceptual Flaws of Constant Product Automated Market Making, working paper dated June 8, 2021, pp. 14–15, §II.C, Lemma 2, (3); p. 14, display after (2) (p^tmm)

import Mathlib

namespace CPAMMFlaws.Properties

/-- Equation (3), Lemma 2, p. 15: the amount of token B paid to trade `x` units of token A
against a constant product pool holding `X` units of A and `Y` units of B,
`p^cmm(x, X, Y) = x * Y / (X - x)`. A negative `x` is a sale, and the negative cost is
minus the revenue earned (p. 16). -/
noncomputable def pcmm (x X Y : ℝ) : ℝ := x * Y / (X - x)

/-- The linear ("traditional") market maker's total cost for buying `x` units when the
`N` market makers hold combined inventory `I`, with fundamental value `V` and liquidity
factor `ℓ` (p. 14): `p^tmm(x, I) = x (V - (ℓ/N) I) + (ℓ/(2N)) x²`. -/
noncomputable def ptmm (x V ℓ N I : ℝ) : ℝ := x * (V - ℓ / N * I) + ℓ / (2 * N) * x ^ 2

end CPAMMFlaws.Properties


