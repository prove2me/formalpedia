-- Prove2me | Definitions.Def_ZORiem_RGD_Algorithm
-- name    : ZORiem_RGD_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:30.947753+00:00
-- url     : https://prove2.me/theorems/d07e506c-c671-4be4-8d3b-952d174c35a0
-- title:
--   Algorithm 1 (ZO-RGD), p. 14, and the constant C(µ) of Theorem 3.1, p. 15
-- statement:
--   Let $E$, $M$, $R$, $f$ and $g_\mu$ be as in Definition 2.6, let $\eta>0$ be a step size and $x_0\in M$. Let $(u_0^k)_{k\ge0}$ be a sequence of vectors of $E$; in the paper they are independent standard Gaussian vectors $N(0,I_n)$. **Algorithm 1 (ZO-RGD)** generates
--
--   $$x_{k+1}=R_{x_k}\big(-\eta\,g_\mu(x_k)\big),\qquad g_\mu(x_k)=\frac{f\big(R_{x_k}(\mu P_{x_k}u_0^k)\big)-f(x_k)}{\mu}\,P_{x_k}u_0^k ,$$
--
--   so that $u_k=P_{x_k}u_0^k$ is the projection of the $k$-th Gaussian draw onto the tangent space at the current iterate. Three objects are defined:
--
--   1. `iterate`: the sequence $(x_k)_{k\in\mathbb N}$ as a function of $k$ and of the whole draw sequence $\omega=(u_0^k)_k$;
--   2. `gaussSeq E`: the law of the draws, the infinite product of standard Gaussian measures on $E$;
--   3. `Cmu L µ d`: the constant of Theorem 3.1,
--   $$C(\mu)=\frac{\mu^2L}{16}\frac{(d+3)^3}{d+4}+\frac{\mu^2L}{16}\frac{(d+6)^3}{d+4}+\frac{\mu^2L}{16}\frac{(d+6)^3}{(d+4)^2}.$$
--
--   The iterate sequence is the algorithm run without a stopping time, so $x_k$ exists for every $k$; Theorem 3.1 sums over $k=0,\dots,N$.
--
--   **Formalization Note** The middle term of `Cmu` carries the factor $L$; the paper prints $\frac{\mu^2}{16}\frac{(d+6)^3}{d+4}$, which comes from the printed Proposition 2.1(b) with $L$ in place of $L^2$. The proof of Theorem 3.1 with the corrected Proposition 2.1(b) gives the term with $L$.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Algorithm 1, p. 14; Theorem 3.1 (C(µ)), p. 15

import Mathlib
import Definitions.Def_ZORiem_RGD_zoGrad

namespace ZORiem.RGD

open MeasureTheory ProbabilityTheory

/-- Algorithm 1 (ZO-RGD), p. 14, run without a stopping time: `x_0 = x₀` and
`x_{k+1} = R_{x_k}(-η g_µ(x_k))`, where the estimator at step `k` uses the `k`-th Gaussian draw
`ω k ∈ E` (so `u_k = P_{x_k}(ω k)`, projected at the current iterate). -/
noncomputable def iterate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Set E) (R : E → E → E) (f : E → ℝ) (mu η : ℝ) (x₀ : E) :
    ℕ → (ℕ → E) → E
  | 0, _ => x₀
  | k + 1, ω =>
      R (iterate M R f mu η x₀ k ω) (-η • zoGrad M R f mu (iterate M R f mu η x₀ k ω) (ω k))

/-- The law of the Gaussian draws of Algorithm 1: an i.i.d. sequence `(u₀^k)_{k ∈ ℕ}` of standard
Gaussian vectors of `E` (`N(0, I_n)`), i.e. the infinite product of `stdGaussian E`. -/
noncomputable def gaussSeq (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (ℕ → E) :=
  Measure.infinitePi (fun _ : ℕ => stdGaussian E)

/-- The constant `C(µ)` of Theorem 3.1, p. 15, in the form the proof derives with the `L²` of
Proposition 2.1(b) (the printed middle term `µ²(d+6)³/(16(d+4))` lacks the factor `L`):
`C(µ) = µ²L(d+3)³/(16(d+4)) + µ²L(d+6)³/(16(d+4)) + µ²L(d+6)³/(16(d+4)²)`. -/
noncomputable def Cmu (L mu : ℝ) (d : ℕ) : ℝ :=
  mu ^ 2 * L * ((d : ℝ) + 3) ^ 3 / (16 * ((d : ℝ) + 4)) +
    mu ^ 2 * L * ((d : ℝ) + 6) ^ 3 / (16 * ((d : ℝ) + 4)) +
    mu ^ 2 * L * ((d : ℝ) + 6) ^ 3 / (16 * ((d : ℝ) + 4) ^ 2)

end ZORiem.RGD


