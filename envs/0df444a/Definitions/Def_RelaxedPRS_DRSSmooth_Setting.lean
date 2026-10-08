-- Prove2me | Definitions.Def_RelaxedPRS_DRSSmooth_Setting
-- name    : RelaxedPRS_DRSSmooth_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:31.168321+00:00
-- url     : https://prove2.me/theorems/9841709f-e8e5-4490-86a3-23ca63546e98
-- title:
--   §1.2–§1.9 — relaxed PRS, DRS, proximal points, objective error and (3.1)
-- statement:
--   Let $H$ be a real Hilbert space. Given proximal maps $P_f=\operatorname{prox}_{\gamma f}$ and $P_g=\operatorname{prox}_{\gamma g}$, reflection through $P$ is $R_P(z)=2P(z)-z$, and the Peaceman–Rachford map is $T_{\mathrm{PRS}}=R_{P_f}\circ R_{P_g}$. A relaxed run satisfies
--   $$z^{k+1}=(1-\lambda_k)z^k+\lambda_k T_{\mathrm{PRS}}(z^k).$$
--   The two proximal points are $x_g(z)=P_g(z)$ and $x_f(z)=P_f(R_{P_g}(z))$. Their proximal subgradients are $(z-x_g(z))/\gamma$ and $(R_{P_g}(z)-x_f(z))/\gamma$. For DRS, $\lambda_k=1/2$.
--
--   For real-valued $g$, the objective error at $x_f^k$ relative to a fixed point $z^*$ is $e_k=f(x_f^k)+g(x_f^k)-f(x^*)-g(x^*)$, where $x^*=P_g(z^*)$. The summand of (3.1) adds weighted squared gradient and proximal-point increments to $2\gamma e_k$.
--
--   These definitions fix the algorithm and objective used by the rate theorems.
--
--   **Formalization Note** Extended-real $f$ is converted to a real value only at proximal outputs; under the stated properness and proximal-map hypotheses these outputs are in $\operatorname{dom}f$.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, pp. 4–7, 11, §1.2, §1.4, Algorithm 1, Lemma 1.1, (3.1)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_RelaxedPRS_StrongCvx_Setting

open InnerProductSpace

namespace RelaxedPRS.DRSSmooth

/-- The real function g regarded as an extended-real function. -/
def gE {H : Type*} (g : H → ℝ) : H → EReal := fun x => (g x : EReal)

/-- Objective error at the second proximal point relative to a fixed point, §3.2. -/
noncomputable def errF {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (g : H → ℝ) (Pf Pg : H → H) (z : ℕ → H) (zs : H)
    (k : ℕ) : ℝ :=
  (f (RelaxedPRS.StrongCvx.xf Pf Pg (z k))).toReal + g (RelaxedPRS.StrongCvx.xf Pf Pg (z k)) -
    (f (RelaxedPRS.StrongCvx.xg Pg zs)).toReal - g (RelaxedPRS.StrongCvx.xg Pg zs)

/-- The summand in (3.1), evaluated at the fixed point. -/
noncomputable def seqB {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → EReal) (g : H → ℝ) (Pf Pg : H → H)
    (z : ℕ → H) (zs : H) (γ β θ : ℝ) (i : ℕ) : ℝ :=
  2 * γ * errF f g Pf Pg z zs i +
    θ * γ ^ 2 * ‖gradient g (RelaxedPRS.StrongCvx.xg Pg (z (i + 1))) - gradient g (RelaxedPRS.StrongCvx.xg Pg (z i))‖ ^ 2 +
    (1 - θ) * γ ^ 2 / β ^ 2 * ‖RelaxedPRS.StrongCvx.xg Pg (z (i + 1)) - RelaxedPRS.StrongCvx.xg Pg (z i)‖ ^ 2

end RelaxedPRS.DRSSmooth


