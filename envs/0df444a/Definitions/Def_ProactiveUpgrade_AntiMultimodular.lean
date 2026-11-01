-- Prove2me | Definitions.Def_ProactiveUpgrade_AntiMultimodular
-- name    : ProactiveUpgrade_AntiMultimodular
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:51:10.695003+00:00
-- url     : https://prove2.me/theorems/0b654a8c-5b92-4b9d-be36-d51088141cdc
-- title:
--   Anti-multimodular functions on $\mathbb N^n$
-- statement:
--   A function $f$ is **anti-multimodular** with respect to $\mathcal F$ if for all $x$ and all $a,b\in\mathcal F$ with $a\ne b$,
--
--   $$
--   f(x+a)+f(x+b)\le f(x)+f(x+a+b).\qquad\text{(A.1)}
--   $$
--
--   Anti-multimodularity is the property of the value function that yields the threshold structure of the optimal upgrade policy (Proposition 4, Theorem 3).
--
--   **Formalization Note** The paper writes $f:\mathbb Z^m\to\mathbb R$, but its value functions are defined only on inventories $x\ge0$ and its proofs treat exactly the quadrant. Here $f$ is a function on $\mathbb N^n$ and (A.1) is required whenever the four points $x$, $x+a$, $x+b$, $x+a+b$ lie in $\mathbb N^n$ (the first and last follow from the other two for distinct generators). This is Definition A.1 for the extension of $f$ by $-\infty$ outside the quadrant. For $n=0$ the condition is empty; for $n=1$ it is concavity.
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Definition A.1, p.31

import Mathlib
import Definitions.Def_ProactiveUpgrade_Dir
import Definitions.Def_ProactiveUpgrade_Gen

namespace ProactiveUpgrade

/-- **Anti-multimodularity** (Chen et al., SSRN 3777846, Definition A.1, p.31): `f` is
anti-multimodular with respect to `𝓕` if for all `x` and `a, b ∈ 𝓕` with `a ≠ b`,
`f(x + a) + f(x + b) ≤ f(x) + f(x + a + b)`  (A.1).

**Formalization Note** The paper writes `f : ℤᵐ → ℝ`, but its value functions `v̂ₜ` are defined only
on inventories `x ≥ 0` (p.10), and its proofs treat exactly the quadrant (Case 1, p.37, excludes
`a, b ∈ {−e₁, d₂}` at `x₁ = x₂ = 0` because they leave it). So `f` is a function on `ℕⁿ` and (A.1)
is required whenever the four points `x, x + a, x + b, x + a + b` lie in `ℕⁿ` (the first and last
follow from the middle two for distinct generators). This is Definition A.1 for the extension of
`f` by `−∞` off the quadrant. For `n = 0` the condition is empty; for `n = 1` it is concavity. -/
def AntiMultimodular {n : ℕ} (f : (Fin n → ℕ) → ℝ) : Prop :=
  ∀ (x a b : Fin n → ℤ), a ∈ gens n → b ∈ gens n → a ≠ b →
    InQuad x → InQuad (x + a) → InQuad (x + b) → InQuad (x + a + b) →
      liftZ f (x + a) + liftZ f (x + b) ≤ liftZ f x + liftZ f (x + a + b)

end ProactiveUpgrade


