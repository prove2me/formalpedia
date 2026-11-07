-- Prove2me | Definitions.Def_ApproxDegComp_IsApprox
-- name    : ApproxDegComp_IsApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:44.78307+00:00
-- url     : https://prove2.me/theorems/1db8f8da-9f62-464e-b1fc-61d15cbce926
-- title:
--   $\varepsilon$-approximating polynomial of a Boolean function
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ be a Boolean function and $\varepsilon\ge 0$. A real polynomial $p:\mathbb R^n\to\mathbb R$ **$\varepsilon$-approximates** $f$ if
--
--   $$|p(x)-f(x)|\le\varepsilon\qquad\text{for every }x\in\{0,1\}^n .$$
--
--   This is the approximation notion underlying the approximate degree.
--
--   **Formalization Note** $p$ is any real multivariate polynomial (not necessarily multilinear), evaluated at the 0/1 points. The range $0\le\varepsilon<1/2$ of Definition 2 is not built into the predicate; each statement fixes or bounds $\varepsilon$.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Definition 2, p.11

import Mathlib
import Definitions.Def_ApproxDegComp_cubePt

namespace ApproxDegComp

/-- **ε-approximating polynomial** (Definition 2, p.11).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Definition 2, p.11: "For 0 ≤ ϵ < 1/2, a real polynomial p : ℝⁿ → ℝ is said to approximate f
if |p(x) − f(x)| ≤ ϵ, for every x ∈ {0, 1}ⁿ."

`IsApprox ε f p` says that the real polynomial `p` (in the variables `ι`) is within `ε` of
`f` at every point of the Boolean cube.

**Formalization Note** Polynomials are `MvPolynomial ι ℝ` of any shape (not only multilinear
ones), evaluated at the 0/1 point `cubePt x`. The range `0 ≤ ε < 1/2` of Definition 2 is not
bundled into the predicate: every statement of the mission uses `ε = 1/3` or states its range. -/
def IsApprox {ι : Type} (ε : ℝ) (f : (ι → Bool) → Bool) (p : MvPolynomial ι ℝ) : Prop :=
  ∀ x : ι → Bool, |MvPolynomial.eval (cubePt x) p - boolToReal (f x)| ≤ ε

end ApproxDegComp


