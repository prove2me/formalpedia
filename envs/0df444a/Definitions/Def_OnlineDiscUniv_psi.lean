-- Prove2me | Definitions.Def_OnlineDiscUniv_psi
-- name    : OnlineDiscUniv_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:48.638737+00:00
-- url     : https://prove2.me/theorems/b54b7216-b8e9-4483-aa0a-e6b0d30ab0ab
-- title:
--   Steering function $\psi_\rho(x)=(\rho/m_\delta)\tanh(Lx)$, $m_\delta=\mathbb E[G\tanh(LG)]$ and $a_\delta$
-- statement:
--   Let $G\sim N(0,1)$ and $L>0$. Set $m_\delta:=\mathbb E[G\tanh(LG)]$ (3.4), and for $\rho\ge0$
--   $$
--   \psi_\rho(x):=\frac{\rho}{m_\delta}\tanh(Lx)\quad(3.5),\qquad a_\delta:=\frac{c_*-\delta}{c_*-\delta/2}\quad(3.6).
--   $$
--   The sign rule (3.16) chooses $\varepsilon=+1$ with conditional probability $\tfrac12(1+\psi_\rho(\langle v,\zeta\rangle))$; when $L$ satisfies (3.4) and $\rho\le c_*-\delta$, $|\psi_\rho|\le a_\delta<1$.
--
--   **Formalization Note** The paper writes $m_\delta$ because $L=L_\delta$ is chosen from $\delta$; here $m_\delta$ is a function of $L$. The Gaussian expectation is a Bochner integral of an integrable function.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), (3.3)–(3.6), p.7 (PDF p.8)

import Mathlib
import Definitions.Def_OnlineDiscUniv_Ralpha

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace OnlineDiscUniv

/-- `m := E[G tanh(LG)]` for `G ∼ N(0,1)` (Jo–Lee, arXiv:2610.00103, artifact sha256
cb190f12…, (3.4), printed p.7, PDF p.8; written `m_δ` there because `L = L_δ`).

**Formalization Note** The integrand is bounded by `|x|`, which is Gaussian-integrable, so the
Bochner integral is the true expectation. -/
noncomputable def mL (L : ℝ) : ℝ := ∫ x, x * Real.tanh (L * x) ∂(gaussianReal 0 1)

/-- The steering function `ψ_ρ(x) := (ρ/m_δ) tanh(Lx)` (Jo–Lee, arXiv:2610.00103, (3.5), p.7,
PDF p.8), with `m_δ = mL L`. -/
noncomputable def psi (L ρ x : ℝ) : ℝ := ρ / mL L * Real.tanh (L * x)

/-- `a_δ := (c_* − δ)/(c_* − δ/2)` (Jo–Lee, arXiv:2610.00103, (3.6), p.7, PDF p.8). -/
noncomputable def aDelta (δ : ℝ) : ℝ := (cStar - δ) / (cStar - δ / 2)

end OnlineDiscUniv


