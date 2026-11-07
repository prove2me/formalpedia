-- Prove2me | Definitions.Def_BeatingGV42_Psi
-- name    : BeatingGV42_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:00.357519+00:00
-- url     : https://prove2.me/theorems/ef0ca0bf-7e66-4139-8676-f9862a6574b9
-- title:
--   The constant $\kappa$ and the exponent $\Psi_{a,q}(t,x)$
-- statement:
--   Let $Q$ be a square prime power and $2\le q\le Q$. Set
--   $$
--   \kappa=\frac{\ln Q}{\sqrt Q-1}-\ln(1-1/Q),
--   $$
--   and for $a$ real and $(t,x)\in(0,1)^2$
--   $$
--   \Psi_{a,q}(t,x)=h(x)-(a+x-1)\ln t-(1-x)\ln(1-t)-\kappa+x\ln\frac{q-1}{Q-1},
--   \qquad h(x)=-x\ln x-(1-x)\ln(1-x).
--   $$
--   $\Psi_{a,q}(t,w/N)$ is the exponential growth rate, per rational place, of the bound on the expected number of surviving low-weight codewords (eq. (4.22)); Proposition 4.9 asks for some $t$ with $\Psi_{a,q}(t,\delta)<0$.
--
--   **Formalization Note** `kappa Q` and `Psi Q q a t x` with $Q,q$ natural numbers cast to $\mathbb R$ and natural logarithms; $h$ is Mathlib's `Real.binEntropy`. The expression is defined on all of $\mathbb R^2$; statements restrict $(t,x)$ to $(0,1)^2$ or evaluate at $t=1/49$, where the paper also does.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §4.4, p.20 (PDF p.22)

import Mathlib

set_option autoImplicit false

namespace BeatingGV42

/-- **The constant `κ = ln Q/(√Q − 1) − ln(1 − 1/Q)`** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.4, p.20 (PDF p.22)). By Lemma 4.8 it
is the limit of `ln h_{F_i}/N_i` along an asymptotically optimal sequence.

**Formalization Note** `Q : ℕ` is cast to `ℝ`; natural logarithms throughout. The paper takes `Q` a
square prime power (`Q ≥ 4`), so `√Q − 1 > 0` and `1 − 1/Q > 0`. -/
noncomputable def kappa (Q : ℕ) : ℝ :=
  Real.log Q / (Real.sqrt Q - 1) - Real.log (1 - 1 / (Q : ℝ))

/-- **The exponent `Ψ_{a,q}(t, x)`** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.4, p.20 (PDF p.22)):
`Ψ_{a,q}(t, x) = h(x) − (a + x − 1) ln t − (1 − x) ln(1 − t) − κ + x ln((q − 1)/(Q − 1))`, where
`h(x) = −x ln x − (1 − x) ln(1 − x)` and `κ = kappa Q`.

**Formalization Note** `h` is Mathlib's `Real.binEntropy` (`x ln x⁻¹ + (1 − x) ln (1 − x)⁻¹`, the same
function). The paper defines `Ψ_{a,q}` on `(0, 1)²`; here it is the same expression on all of `ℝ²`
(with Mathlib's `Real.log` junk off the positive reals), and every statement restricts `t` and `x`
to `(0, 1)` by hypothesis, or evaluates at `t = 1/49` (§4.5). -/
noncomputable def Psi (Q q : ℕ) (a t x : ℝ) : ℝ :=
  Real.binEntropy x - (a + x - 1) * Real.log t - (1 - x) * Real.log (1 - t) - kappa Q +
    x * Real.log (((q : ℝ) - 1) / ((Q : ℝ) - 1))

end BeatingGV42


