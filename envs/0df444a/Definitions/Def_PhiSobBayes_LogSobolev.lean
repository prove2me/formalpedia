-- Prove2me | Definitions.Def_PhiSobBayes_LogSobolev
-- name    : PhiSobBayes_LogSobolev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:06:36.770199+00:00
-- url     : https://prove2.me/theorems/c0ce8c01-6cf0-4842-ace8-47d12f92ea25
-- title:
--   Log-Sobolev inequality with constant $C$
-- statement:
--   A probability measure $\mu$ on $\mathbb R^n$ **satisfies the log-Sobolev inequality with constant $C$** if
--   $$\mathrm{Ent}_\mu(f^2)\le 2C\,\mathbb E_\mu\|\nabla f\|_2^2\qquad\text{for every } f\in\mathcal A^{\mathbb R_{>0}}_0,\tag{3}$$
--   where $\mathrm{Ent}_\mu(g)=\mathbb E_\mu[g\log g]-\mathbb E_\mu g\,\log\mathbb E_\mu g$ (with $0\log 0=0$). The log-Sobolev constant $C_{\mathrm{LS}}(\mu)$ is the least $C\ge0$ for which this holds.
--
--   It appears in the Bakry–Émery milestone, $C_{\mathrm{LS}}(\mu)\le1/\rho$.
--
--   **Formalization Note** $\mathrm{Ent}_\mu$ is the $\Phi$-entropy for $\Phi(z)=z\log z$; `Real.log 0 = 0` matches the convention $0\log0=0$. "$C_{\mathrm{LS}}(\mu)\le c$" is "`LogSobolev μ c`", as for the Poincaré constant.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Definition 3, p.4 (PDF 4), display (3)

import Mathlib
import Definitions.Def_PhiSobBayes_testClass
import Definitions.Def_PhiSobBayes_phiEnt

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- `μ` satisfies the **log-Sobolev inequality with constant `C`**:
`Ent_μ(f²) ≤ 2C 𝔼_μ ‖∇f‖₂²` for every `f ∈ A^{ℝ>0}_0`, where `Ent_μ(g) = 𝔼_μ[g log g] − 𝔼_μ g log 𝔼_μ g`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Definition 3, p.4 (PDF 4), display (3); the entropy `Ent_μ` on p.4.

**Formalization Note** `Ent_μ` is the Φ-entropy for `Φ(z) = z log z` (`Real.log 0 = 0` gives the
paper's convention `0 log 0 = 0`). The test class is `A^J_0` with `J = (0, ∞)`. The least constant
`C_LS(μ)` is handled as for `Poincare`. -/
def LogSobolev {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (C : ℝ) : Prop :=
  ∀ f ∈ testClass n (Set.Ioi 0),
    phiEnt μ (fun z => z * Real.log z) (fun x => f x ^ 2) ≤ 2 * C * ∫ x, ‖gradient f x‖ ^ 2 ∂μ

end PhiSobBayes


