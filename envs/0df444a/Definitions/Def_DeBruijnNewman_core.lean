-- Prove2me | Definitions.Def_DeBruijnNewman_core
-- name    : DeBruijnNewman_core
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T13:13:20.107918+00:00
-- url     : https://prove2.me/theorems/5cada9b9-2b33-40f9-9ab3-419dfb69622c
-- title:
--   The heat flow $H_t$ of the Riemann $\xi$ function and the constant $\Lambda$
-- statement:
--   This file fixes the three objects the mission is about.
--
--   **The weight.** For $u \in \mathbb{R}$,
--   $$\Phi(u) := \sum_{n=1}^{\infty}\bigl(2\pi^2 n^4 e^{9u} - 3\pi n^2 e^{5u}\bigr)\exp\bigl(-\pi n^2 e^{4u}\bigr),$$
--   the super-exponentially decaying function of equation (3) of the source. In Lean the series is an unconditional `tsum` over the natural numbers with summand evaluated at $n+1$, so it ranges over $n \ge 1$; no convergence claim is built into the definition.
--
--   **The heat flow.** For $t \in \mathbb{R}$ and $z \in \mathbb{C}$,
--   $$H_t(z) := \int_0^{\infty} e^{t u^2}\,\Phi(u)\,\cos(zu)\,du,$$
--   equation (4) of the source, taken as a Bochner integral of a complex-valued function over the open half-line $(0,\infty)$ against Lebesgue measure. The factor $e^{tu^2}\Phi(u)$ is real and is coerced into $\mathbb{C}$; the cosine is the complex cosine. Again, no integrability or analyticity claim is part of the definition. For $t = 0$ one has $H_0(z) = \tfrac18\,\xi\bigl(\tfrac12 + \tfrac{iz}{2}\bigr)$.
--
--   **Real zeros and the de Bruijn-Newman constant.** The predicate `HasOnlyRealZeros t` says that every $z \in \mathbb{C}$ with $H_t(z) = 0$ has vanishing imaginary part, and
--   $$\Lambda := \inf\{\, t \in \mathbb{R} : H_t \text{ has only real zeros} \,\}$$
--   is the de Bruijn-Newman constant. By Newman's theorem the set on the right is the ray $[\Lambda,\infty)$; that theorem is not assumed here, so $\Lambda$ is only the infimum of that set as a real number, with Mathlib's convention for the infimum of an empty or unbounded set.
-- source:
--   B. Rodgers and T. Tao, "The de Bruijn-Newman constant is non-negative", Forum of Mathematics, Pi 8 (2020), e6, https://doi.org/10.1017/fmp.2020.6, Section 1, equations (1)-(4), pp. 2-4

import Mathlib

open MeasureTheory Set

namespace DeBruijnNewman

/-- The super-exponentially decaying function
`Φ(u) = ∑_{n ≥ 1} (2 π² n⁴ e^{9u} − 3 π n² e^{5u}) exp(−π n² e^{4u})`
of Rodgers–Tao, equation (3).  The index `n` below runs over `ℕ`, with the
summand evaluated at `n + 1`, so the sum is over the positive integers. -/
noncomputable def Phi (u : ℝ) : ℝ :=
  ∑' n : ℕ,
    (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u)
        - 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u))
      * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)))

/-- The entire function `H t z = ∫_0^∞ e^{t u²} Φ(u) cos(z u) du`
of Rodgers–Tao, equation (4). -/
noncomputable def H (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), ((Real.exp (t * u ^ 2) * Phi u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))

/-- `H t` has purely real zeros. -/
def HasOnlyRealZeros (t : ℝ) : Prop := ∀ z : ℂ, H t z = 0 → z.im = 0

/-- The de Bruijn–Newman constant `Λ`, defined as the infimum of the set of
times `t` for which `H t` has purely real zeros.  By a theorem of Newman this
set is exactly the ray `[Λ, ∞)`. -/
noncomputable def Lambda : ℝ := sInf {t : ℝ | HasOnlyRealZeros t}

end DeBruijnNewman


