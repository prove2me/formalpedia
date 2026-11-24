-- Prove2me | Definitions.Def_UnfairML_Coverage_Supplement_Success
-- name    : UnfairML_Coverage_Supplement_Success
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:34:07.733799+00:00
-- url     : https://prove2.me/theorems/fce5a699-a209-4f45-a0c3-5d9fc7c04eaf
-- title:
--   §4.3 — protected successful acceptances, failed acceptances and success rate
-- statement:
--   For the protected group with default proportion $d_p$, threshold $c_p$ and effort $s$, let $\phi_p(c_p,s)=\min\{(1-c_p)/(1-\gamma_p s),1\}$ be its published coverage rate. Define
--   $$N_S(c_p,s)=(1-d_p)\phi_p(c_p,s),\qquad N_F(c_p,s)=d_p\max\left\{\frac{1-\gamma_p s-c_p}{1-\gamma_p s},0\right\},$$
--   $$\delta_p(c_p,s)=\frac{N_S(c_p,s)}{N_S(c_p,s)+N_F(c_p,s)}.$$
--   These counts use the unit population of the protected group. The success rate measures the good fraction among accepted candidates and is distinct from coverage among good candidates.
--
--   **Formalization Note** Each ratio uses its own policy's counts. In the proof on p. 45, the stray $d$ is read as $d_p$, and the EO ratio's ET subscripts in the denominator are read as EO subscripts, as required by the verbal definition on p. 21 and the ensuing closed form. Outside positive acceptance, real division has Lean's totalized value; Theorem 3 explicitly concludes that both acceptance denominators are positive.
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 21, success rate; p. 45, proof of Theorem 3

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model

namespace UnfairML.Coverage.Supplement

/-- Protected good candidates accepted, §4.3 and proof of Theorem 3 (pp. 21, 45). -/
noncomputable def successful (P : Params) (cp s : ℝ) : ℝ :=
  (1 - P.dp) * coverage P.γp cp s

/-- Protected bad candidates accepted; `dp` resolves the stray `d` on p. 45. -/
noncomputable def failed (P : Params) (cp s : ℝ) : ℝ :=
  P.dp * max ((1 - P.γp * s - cp) / (1 - P.γp * s)) 0

/-- Successes divided by all acceptances under this same policy. In particular the
EO denominator uses EO counts, as required by p. 21 and the closed form on p. 45. -/
noncomputable def successRate (P : Params) (cp s : ℝ) : ℝ :=
  successful P cp s / (successful P cp s + failed P cp s)

end UnfairML.Coverage.Supplement


