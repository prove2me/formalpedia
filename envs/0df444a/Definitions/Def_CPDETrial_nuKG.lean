-- Prove2me | Definitions.Def_CPDETrial_nuKG
-- name    : CPDETrial_nuKG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:49:30.31397+00:00
-- url     : https://prove2.me/theorems/aebd014e-2090-4ac6-9792-1d7e0c32deae
-- title:
--   cKG allocation indices $\nu^{cKG_{1:\tau}}_i$ (eq. (EC.6))
-- statement:
--   For a lookahead $\tau\ge1$ fixed in advance, the cKG$_{1:\tau}$ index of arm $i$ at the belief $(\mu,\Sigma)$ is
--
--   $$
--   \nu^{cKG_{1:\tau}}_i(\mu,\Sigma)=-1+\frac1{c_i}\,\mathbb E\left[\max_j\left\{\mu_j+\frac{\Sigma_{i,j}}{\Sigma_{i,i}}Z^\tau_i\right\}\right]-\frac1{c_i}\max_j\{\mu_j\},
--   $$
--
--   with $Z^\tau_i\sim N(0,\sigma^2_{Z^\tau_i})$ (eq. (10)): one pays for one sample but uses the information of $\tau$ samples. $\tau=1$ is the cKG$_1$ index. These indices bound the cPDE index from below and above (Lemma EC.1).
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. ec3, eq. (EC.6)

import Mathlib
import Definitions.Def_CPDETrial_zVar
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **The cKG allocation indices `ν^{cKG_{1:τ}}_i(µ^t, Σ^t)`, eq. (EC.6).**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), App. B.4, eq. (EC.6), p. ec3:
"`ν^{cKG_{1:τ}}_i(µ^t,Σ^t) = −1 + (1/c_i) E[max_j{µ^t_j + (Σ^t_{i,j}/Σ^t_{i,i}) Z^τ_i} | µ^t,Σ^t] − (1/c_i) max_j{µ^t_j}`";
`τ = 1` is the cKG₁ index.

The expectation is taken against the law of `Z^τ_i` given in (10), the centred normal law with
variance `zVar λ_i Σ_ii τ`.

**Formalization Note.** Writing the expectation against the law of `Z^τ_i` rather than on a
probability space is an encoding with the same value. The integrand is Lipschitz in `z`, hence
integrable against a Gaussian law. -/
noncomputable def nuKG {M : ℕ} (c : Fin M → ℝ) (lam : Fin M → ℝ≥0) (τ : ℕ) (i : Fin M)
    (m : Fin M → ℝ) (S : Matrix (Fin M) (Fin M) ℝ) : ℝ :=
  -1 + (1 / c i) * ∫ z, (⨆ j, (m j + S i j / S i i * z)) ∂(gaussianReal 0 (zVar (lam i) (S i i) τ))
    - (1 / c i) * ⨆ j, m j

end CPDETrial


