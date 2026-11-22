-- Prove2me | Definitions.Def_AlmostPeriodic_AnalyticStrip
-- name    : AlmostPeriodic_AnalyticStrip
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T18:35:27.457975+00:00
-- url     : https://prove2.me/theorems/da37f722-255f-4dbb-ad01-f1cf55982530
-- title:
--   Almost periodic analytic functions on an open vertical strip $a<\operatorname{Re}s<b$
-- statement:
--   **Almost periodic analytic functions on vertical strips.** For real numbers $a,b$ write $\mathbf C_{(a,b)}=\{s\in\mathbb C: a<\operatorname{Re}s<b\}$ and, for $\alpha\le\beta$, $\mathbf C_{[\alpha,\beta]}=\{s: \alpha\le\operatorname{Re}s\le\beta\}$. A function $f$ is an *almost periodic analytic function on the strip* $\mathbf C_{(a,b)}$ (in the sense of H. Bohr) if
--
--   1. $f$ is holomorphic on $\mathbf C_{(a,b)}$, and
--   2. for every closed substrip $\mathbf C_{[\alpha,\beta]}$ with $a<\alpha$, $\beta<b$, and every $\varepsilon>0$, the set
--   $$\{\tau\in\mathbb R:\ |f(s+i\tau)-f(s)|\le\varepsilon\ \text{ for all } s\in\mathbf C_{[\alpha,\beta]}\}$$
--   is relatively dense in $\mathbb R$ (some $L>0$ is such that every interval $[x,x+L]$ meets it).
--
--   In words: the vertical translates of $f$ approximate $f$ uniformly on each closed substrip, for a relatively dense set of vertical shifts. Examples are vertically periodic holomorphic functions and their finite sums and products with arbitrary (possibly $\mathbb Q$-linearly independent) periods, such as the partial Euler product $\prod_{v\in S_f}(1-q_v^{-s-it_v})$ of (7.1.1.1). Masullo (§7.1.1, pp. 312–313) compares this notion with Bagchi's strong recurrence, which it implies.
--
--   **Formalization Note.** `AlmostPeriodic.IsAlmostPeriodicOnStrip f a b` takes $f:\mathbb C\to\mathbb C$ (its values off the strip are irrelevant) and reuses `AlmostPeriodic.IsRelativelyDense`. For the open strip, uniformity is required on every closed substrip $[\alpha,\beta]\subset(a,b)$ only; this is the convention under which the examples above (functions holomorphic on the open strip, possibly unbounded near its boundary lines) are almost periodic. The paper refers to [Bohr4, Appendix II, §104, p. 101] for the definition.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 312–313, §7.1.1 (almost periodic analytic functions on vertical strips of bounded width); classical reference: H. Bohr, Almost Periodic Functions, Chelsea Publishing Company, New York, 1947 (dated 1933 in the paper's bibliography), Appendix II, §104, p. 101 [Bohr4], as cited by the paper on p. 313.

import Mathlib
import Definitions.Def_AlmostPeriodic_BohrAlmostPeriodic

/-!
# Almost periodic analytic functions on vertical strips

Analytic functions on an open vertical strip `a < Re s < b` that are almost periodic in the
sense of H. Bohr, uniformly on every closed substrip.

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), §7.1.1,
pp. 312–313, which refers to [Bohr4, Appendix II, §104, p. 101] for this notion.
-/

namespace AlmostPeriodic

/-- A function `f : ℂ → ℂ` is an *almost periodic analytic function on the open vertical strip*
`a < Re s < b` if it is holomorphic on that strip and, for every closed substrip
`α ≤ Re s ≤ β` with `a < α` and `β < b` and every `ε > 0`, the set of real numbers `τ` such
that `‖f (s + iτ) - f s‖ ≤ ε` for all `s` in the closed substrip is relatively dense. -/
def IsAlmostPeriodicOnStrip (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  DifferentiableOn ℂ f {s : ℂ | a < s.re ∧ s.re < b} ∧
    ∀ α β : ℝ, a < α → β < b → ∀ ε : ℝ, 0 < ε →
      IsRelativelyDense {τ : ℝ | ∀ s : ℂ, α ≤ s.re → s.re ≤ β →
        ‖f (s + (τ : ℂ) * Complex.I) - f s‖ ≤ ε}

end AlmostPeriodic


