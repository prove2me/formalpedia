-- Prove2me | Definitions.Def_TaoFivePrimes_SmoothedExpSum
-- name    : TaoFivePrimes_SmoothedExpSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-07T08:04:49.699215+00:00
-- url     : https://prove2.me/theorems/30efbeb8-fb86-4988-ac69-9da4bbe78e85
-- title:
--   Tao's smoothed exponential sum $S_{\eta,q_0}(x,\alpha)$
-- statement:
--   Tao's five-primes paper does not work with the sharp-cutoff exponential sum $S(x,\alpha)=\sum_{n\leq x}\Lambda(n)e(\alpha n)$, but with a smoothed variant. For a piecewise smooth cutoff $\eta$ and a modulus $q_0$, Section 1 sets
--
--   $$S_{\eta,q_0}(x,\alpha) \;:=\; \sum_n \Lambda(n)\, e(\alpha n)\, \mathbf 1_{(n,q_0)=1}\, \eta(n/x),$$
--
--   where $e(\theta)=e^{2\pi i\theta}$ and $\Lambda$ is the von Mangoldt function. This is the object estimated by Theorem 1.3, and the factors appearing in the Fourier expression (8.11) for the weighted representation count are instances of it.
--
--   **The modulus.** $q_0$ is described in the paper as being of minor technical importance. Taking $q_0=2$ restricts the sum to odd $n$ and saves a factor of two in the explicit constants; because of that restriction it is $4\alpha$, rather than $\alpha$, that is approximated by a rational $a/q$ in the paper's estimates. Theorem 1.3 imposes the standing hypothesis that every prime factor of $q_0$ is at most $\sqrt x$, which is what admits the choice $q_0=\prod_{p\leq\sqrt x}p$ used at level $x$ in Section 8. That hypothesis belongs on the theorems, not on this definition, so it is not imposed here.
--
--   **The range of summation.** The sum over $n$ is unrestricted rather than a sum over a finite range, following the paper and the mission's stated convention. The cutoffs actually used ($\eta_0$ supported on $[1/4,1]$, $\eta_1$ on $[0.1,0.9]$) are compactly supported away from the origin, so for $x>0$ only finitely many terms are nonzero and the family is summable; the value is the ordinary finite sum.
--
--   **Formalization notes.** The cutoff is taken as $\eta:\mathbb R\to\mathbb R$ rather than the paper's $\mathbb R\to\mathbb C$. Every cutoff used in the paper is real-valued, and this choice lets the existing platform cutoffs `eta0` and `eta1` be substituted without a cast; the complex generality is never used in the estimates. The coprimality condition is `Nat.Coprime n q₀`, which is $\gcd(n,q_0)=1$, so $q_0=1$ imposes no restriction and $q_0=0$ restricts to $n=1$. The auxiliary `expCircle` is the character $e(\theta)$.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Section 1, p. 4, the display defining S_{eta,q_0}(x,alpha) immediately preceding equation (1.7); the q_0 hypothesis is that of Theorem 1.3, p. 5.

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The smoothed exponential sum of Tao's five-primes paper

Source: Terence Tao, https://arxiv.org/abs/1201.6656, Section 1, the display
defining `S_{η,q₀}(x,α)` immediately before equation (1.7).

The sum is unrestricted over `n : ℕ`; the cutoffs used in the paper are compactly
supported away from `0`, so only finitely many terms are nonzero.
-/

open scoped ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- `expCircle θ = e(θ) = exp(2πiθ)`, the additive character of the paper. -/
noncomputable def expCircle (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * θ)

/-- Tao's smoothed exponential sum

`S_{η,q₀}(x, α) = ∑ₙ Λ(n) e(αn) 1_{(n,q₀)=1} η(n/x)`,

for a cutoff `η`, a modulus `q₀`, a scale `x` and a phase `α`. -/
noncomputable def smoothedExpSum (η : ℝ → ℝ) (q₀ : ℕ) (x α : ℝ) : ℂ :=
  ∑' n : ℕ,
    if Nat.Coprime n q₀ then
      (Λ n : ℂ) * expCircle (α * n) * (η ((n : ℝ) / x) : ℂ)
    else 0

end TaoFivePrimes


