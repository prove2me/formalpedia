-- Prove2me | Definitions.Def_MarkovCLTRate_Stein
-- name    : MarkovCLTRate_Stein
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:25:25.830826+00:00
-- url     : https://prove2.me/theorems/8aad6083-9fa4-45f3-ac1b-bd0067e83dae
-- title:
--   The Stein solution (Mehler form), the constants $\tilde C_1,\tilde C_2$, Gaussian smoothing $P_A h$ and the matrix $A_{k,h}$
-- statement:
--   Let $Z\sim N(0,I)$ be a standard Gaussian vector in $\Re^d$ and $c_t=\sqrt{1-e^{-2t}}$. For a Lipschitz function $g:\Re^d\to\Re$, the solution of **Stein's equation**
--   $$
--   g(u)-E(g(Z))=\Delta f(u)-u^T\nabla f(u)\qquad(2)
--   $$
--   used in the paper is the Mehler solution
--   $$
--   f(u)=-\int_0^\infty\Big(E\big[g(e^{-t}u+c_tZ)\big]-E[g(Z)]\Big)\,dt .
--   $$
--   The constants of Lemma 1 are
--   $$
--   C_1(d)=2^{3/2}\frac{(1+2d)\Gamma((1+d)/2)}{d\,\Gamma(d/2)},\quad C_2(d)=2\sqrt{\frac{2d}{\pi}},\quad \tilde C_1(d,\beta)=C_1(d)+\frac{2}{1-\beta},\quad \tilde C_2(d,\beta)=C_2(d)+\frac{2d}{1-\beta}.
--   $$
--   For a covariance matrix $A$, **Gaussian convolution** is $P_Ah(x)=E[h(x+A^{1/2}Z)]$.
--
--   Finally, for $h\in Lip_1$, a shift $a\in\Re^d$, a matrix $Q$ (in the paper $Q_k=V_k^{1/2}$) and a covariance $\Lambda$ (in the paper $\Lambda_k=V_k^{-1/2}V_{k+1}V_k^{-1/2}$), let $f_{a}$ be the Stein solution for $\tilde h(u)=h(a+Qu)$ and set
--   $$
--   A_{k,h}(a)=E\big[\nabla^2 f_{a}(\tilde Z)\big],\qquad \tilde Z\sim N(0,\Lambda).
--   $$
--   Evaluated at $a=S_{k-1}$, this is the matrix $A_{k,h}(\mathcal F_{k-1})$ of Theorem 1.
--
--   **Formalization Note** The outer integral of the Mehler formula is over $t\in(0,\infty)$. $P_Ah(x)$ is written as $\int h(x+y)\,dN(0,A)(y)$ with `multivariateGaussian 0 A`, the law of $A^{1/2}Z$. $A_{k,h}$ is taken entrywise. In the paper $A_{k,h}(\mathcal F_{k-1})=E[\nabla^2f_{k,h}(\tilde Z_k)\mid\mathcal F_{k-1}]$ with $\tilde Z_k$ independent of $\mathcal F_{k-1}$ and $f_{k,h}$ determined by $S_{k-1}$; this conditional expectation is the function above at $a=S_{k-1}$.
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, Lemma 1 and (2), p.5; proof of Theorem 1, pp.6–8; proof of Lemma 3, p.11 (Mehler representation, c_t, P_A h)

import Mathlib
import Definitions.Def_MarkovCLTRate_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- The solution of Stein's equation (2) for the standard Gaussian, arXiv:2401.15719v5, Lemma 1,
p.5, in the Mehler form named on p.11:
`f(u) = −∫_0^∞ ( E[g(e^{−t}u + c_t Z)] − E[g(Z)] ) dt`, with `c_t = √(1 − e^{−2t})` and
`Z ∼ N(0, I)`. For Lipschitz `g` it solves
`g(u) − E[g(Z)] = Δf(u) − uᵀ∇f(u)` (Lemma 1 asserts this).

**Formalization Note.** Stein's equation determines its solution only up to an additive
constant in the class used; "the solution" of Lemma 1 is the Mehler one, which the paper uses on
p.11. -/
noncomputable def steinSolution {d : ℕ} (g : Vec d → ℝ) (u : Vec d) : ℝ :=
  -∫ t in Set.Ioi (0 : ℝ),
      ((∫ z, g (Real.exp (-t) • u + Real.sqrt (1 - Real.exp (-2 * t)) • z) ∂(stdGaussian (Vec d)))
        - ∫ z, g z ∂(stdGaussian (Vec d)))

/-- `C₁(d) = 2^{3/2} (1 + 2d) Γ((1+d)/2) / (d Γ(d/2))`, arXiv:2401.15719v5, Lemma 1, p.5. -/
noncomputable def C1 (d : ℕ) : ℝ :=
  (2 : ℝ) ^ ((3 : ℝ) / 2) * (1 + 2 * (d : ℝ)) * Real.Gamma ((1 + (d : ℝ)) / 2)
    / ((d : ℝ) * Real.Gamma ((d : ℝ) / 2))

/-- `C₂(d) = 2 √(2d/π)`, arXiv:2401.15719v5, Lemma 1, p.5. -/
noncomputable def C2 (d : ℕ) : ℝ := 2 * Real.sqrt (2 * (d : ℝ) / Real.pi)

/-- `C̃₁(d, β) = C₁(d) + 2/(1 − β)`, arXiv:2401.15719v5, Lemma 1, p.5. -/
noncomputable def C1t (d : ℕ) (β : ℝ) : ℝ := C1 d + 2 / (1 - β)

/-- `C̃₂(d, β) = C₂(d) + 2d/(1 − β)`, arXiv:2401.15719v5, Lemma 1, p.5. -/
noncomputable def C2t (d : ℕ) (β : ℝ) : ℝ := C2 d + 2 * (d : ℝ) / (1 - β)

/-- Gaussian convolution with covariance `A`, arXiv:2401.15719v5, proof of Lemma 3, p.11:
`P_A h(x) = E[h(x + A^{1/2} Z)]`, `Z ∼ N(0, I)`.

**Formalization Note.** `A^{1/2}Z` has law `multivariateGaussian 0 A` (Mathlib builds that measure
as the image of `N(0, I)` under `A^{1/2}`), so `P_A h(x) = ∫ h(x + y) dN(0, A)(y)`. -/
noncomputable def gaussSmooth {d : ℕ} (A : Mat d) (h : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ y, h (x + y) ∂(multivariateGaussian 0 A)

/-- The matrix `A_{k,h}` of Theorem 1, arXiv:2401.15719v5, p.6, as a function of the shift
`a = S_{k−1}`:
`A_{k,h}(a) = E[∇²f_{k,h}(Z̃_k)]`, where `f_{k,h}` is the Stein solution for
`h̃_k(u) = h(a + Q_k u)` with `Q_k = V_k^{1/2}` (proof of Theorem 1, p.7), and
`Z̃_k ∼ N(0, Λ_k)`, `Λ_k = V_k^{−1/2} V_{k+1} V_k^{−1/2}`.

Here `Q` is `Q_k` and `Λ` is `Λ_k`; the expectation is taken entrywise.

**Formalization Note.** On p.6 `A_{k,h}(𝓕_{k−1}) = E[∇²f_{k,h}(Z̃_k) | 𝓕_{k−1}]` with `Z̃_k`
independent of `𝓕_{k−1}` and `f_{k,h}` determined by `S_{k−1}`; this conditional expectation is
the function below evaluated at `a = S_{k−1}`, so no extension of the probability space is
needed. -/
noncomputable def steinA {d : ℕ} (h : Vec d → ℝ) (Q Λ : Mat d) (a : Vec d) : Mat d :=
  Matrix.of fun i j =>
    ∫ z, hessMat (steinSolution (fun u => h (a + mApply Q u))) z i j ∂(multivariateGaussian 0 Λ)

end MarkovCLTRate


