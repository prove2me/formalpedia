-- Prove2me | Definitions.Def_ScarceIdeas_welfare
-- name    : ScarceIdeas_welfare
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:55.065909+00:00
-- url     : https://prove2.me/theorems/4011e519-60af-4c83-a2d8-7c1c664f6dbb
-- title:
--   Expected social welfare $J(\phi,u)$ of a policy (corrected (16))
-- statement:
--   Let $r>0$ be the discount rate and $v/r$ the social value of filling the niche. Starting from the state $\phi$ with beliefs $h_\phi$, the expected discounted social welfare of the policy $u$ is
--
--   $$J(\phi,u)=\int_0^\infty e^{-rt}\,\frac{\int_0^\infty\lambda h_0(\lambda)e^{-\lambda\Phi(t)}\,d\lambda}{Z(\phi)}\int_{\underline c}^{u(t)}\Bigl(\frac vr-c\Bigr)f(c)\,dc\;dt ,$$
--
--   where $\Phi$ is the state path of $u$. The inner cost integral equals $(v/r-E(c\mid u(t)))F(u(t))$, and the $\lambda$-integral divided by $Z(\phi)$ is the expected arrival rate times the survival probability, $m_1(\Phi(t))Z(\Phi(t))/Z(\phi)$.
--
--   **Formalization Note** This is (16) corrected: the page multiplies $e^{-\lambda\phi(t)}$ by $h_{\phi(t)}(\lambda)$, which already contains $e^{-\lambda\phi(t)}$. The corrected form is the continuous-time limit of the Bellman recursion (17) that the paper solves. For $h_0(\lambda)=e^{-\lambda}$ and $F(p)=1/2$, the printed $\lambda$-integrand at $\phi(t)=1$ integrates to $(1/2)\cdot2/9$ instead of the Bayesian claim density $(1/2)\cdot1/4$.
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §4.2, (16)–(17), pp.20–21

import Mathlib
import Definitions.Def_ScarceIdeas_normalizer
import Definitions.Def_ScarceIdeas_statePath

namespace ScarceIdeas

/-- **Expected social welfare of a reward policy from state `ϕ` (corrected (16)).**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§4.2, (16), p.20, as the continuous-time limit of the Bellman recursion (17), p.21.

With beliefs `h_ϕ` at the start, discount rate `r`, social value `v/r`, and state path
`Φ(t) = ϕ + ∫_0^t F(u(s)) ds`,

$$J(\phi,u)=\int_0^\infty e^{-rt}\,
\frac{\int_0^\infty \lambda h_0(\lambda)e^{-\lambda\Phi(t)}\,d\lambda}{Z(\phi)}\,
\int_{\underline c}^{u(t)}\Bigl(\frac vr-c\Bigr)f(c)\,dc\;dt .$$

Here `∫_{c̲}^{p}(v/r − c) f(c) dc = (v/r − E(c|p)) F(p)` is the expected net value of a viable idea
times its probability, and `∫ λ h0(λ) e^{−λΦ(t)} dλ / Z(ϕ) = m₁(Φ(t)) · Z(Φ(t))/Z(ϕ)` is the expected
arrival rate times the survival probability under the beliefs `h_ϕ`.

**Formalization Note** This corrects (16) as printed, which multiplies `e^{−λϕ(t)}` by
`h_{ϕ(t)}(λ)`, a density that already contains the factor `e^{−λϕ(t)}`; the corrected form is the
one the Bellman equation (17) and every later step of the paper use. `(v/r − E(c|p)) F(p)` is
written as one integral, so no division by `F(p) = 0` occurs. -/
noncomputable def welfare (r v cL : ℝ) (f h0 : ℝ → ℝ) (ϕ : ℝ) (u : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Ioi 0, Real.exp (-r * t) *
    ((∫ lam in Set.Ioi 0, lam * h0 lam * Real.exp (-lam * statePath cL f ϕ u t)) /
      normalizer h0 ϕ) *
    ∫ c in cL..u t, (v / r - c) * f c

end ScarceIdeas


