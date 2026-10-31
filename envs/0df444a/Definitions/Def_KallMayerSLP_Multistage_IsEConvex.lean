-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_IsEConvex
-- name    : KallMayerSLP_Multistage_IsEConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:02.680044+00:00
-- url     : https://prove2.me/theorems/614f3fb7-8734-4ef9-8253-0f08f61a0780
-- title:
--   Convexity of an extended-real-valued function
-- statement:
--   A function $f$ from a real vector space to $[-\infty,+\infty]$ is convex if $f(ax+by)\le af(x)+bf(y)$ for all $x,y$ and all $a,b\ge0$ with $a+b=1$. Taken on the product of the decision and realization spaces, this is the book's "jointly convex".
--
--   **Formalization Note** Extended-real arithmetic: $0\cdot(\pm\infty)=0$ and $(-\infty)+(+\infty)=-\infty$. The latter does not occur for the functions of this mission, which do not take the value $+\infty$ at stages $t\ge2$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, p.264 (PDF 273)

import Mathlib

namespace KallMayerSLP.Multistage

/-- Convexity of an extended-real-valued function on a real vector space: for `a, b ≥ 0`,
`a + b = 1`, `f(a x + b y) ≤ a f(x) + b f(y)`. This is the "jointly convex" of Kall & Mayer,
*Stochastic Linear Programming* (2005), Chapter 3, p.264, PDF 273, taken on the product of the
decision and the realization spaces.

**Formalization Note.** `EReal` arithmetic: `0 * (±∞) = 0`, and `(-∞) + (+∞) = -∞`. The latter never
occurs for the functions of this mission at stages `t ≥ 2`, which do not take the value `+∞`. -/
def IsEConvex {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → EReal) : Prop :=
  ∀ x y : E, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y

end KallMayerSLP.Multistage


