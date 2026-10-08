-- Prove2me | Definitions.Def_LogSobolevMC_Metropolis_Setting
-- name    : LogSobolevMC_Metropolis_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:34.055328+00:00
-- url     : https://prove2.me/theorems/de757d7b-887d-40ab-a30b-770e4b943d29
-- title:
--   §2.2, p. 702 — the smallest eigenvalue β_min of a reversible chain, in Rayleigh-quotient form
-- statement:
--   Let $\mathcal X$ be a finite set, $K$ a Markov kernel on $\mathcal X$ (a matrix with $K(x,y)\ge 0$ and $\sum_y K(x,y)=1$) and $\pi$ an invariant probability measure for $K$ charging every point. Functions are real valued, $Kf(x)=\sum_y K(x,y)f(y)$, and $\langle f,g\rangle=\sum_x f(x)g(x)\pi(x)$.
--
--   When $(K,\pi)$ is reversible, $K$ is self-adjoint on $\ell^2(\pi)$ and has real eigenvalues $-1\le\beta_{\min}=\beta_{|\mathcal X|-1}\le\dots\le\beta_1\le\beta_0=1$. This file defines the **smallest eigenvalue** in its variational form
--   $$\beta_{\min}=\inf\Big\{\frac{\langle Kf,f\rangle}{\langle f,f\rangle}: f\neq 0\Big\}.$$
--
--   The quantity $1+\beta_{\min}$ controls the periodic behaviour of the discrete-time chain; together with the spectral gap it enters the discrete-time convergence bound through $\lambda_*=\min\{\lambda,1+\beta_{\min}\}$.
--
--   **Formalization Note** The infimum is a real `sInf`. For a stochastic $K$ with invariant $\pi$ the quotient set is nonempty and contained in $[-1,1]$, so the value is a genuine infimum. It equals the smallest eigenvalue of $K$ when $(K,\pi)$ is reversible, the only case in which the paper uses it. The Dirichlet form, the $\ell^p(\pi)$ norms, $\mathcal L(f)$, the spectral gap $\lambda$ and the log-Sobolev constant $\alpha$ are the shared definitions of `LogSobolevMC.ChiSquare.Setting`, imported here.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 702, §2.2 (β_min)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_mm_spectral
import Definitions.Def_LogSobolevMC_ChiSquare_Setting
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Metropolis

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The smallest eigenvalue `β_min` of a reversible chain (§2.2, p. 702), in its
variational (Rayleigh quotient) form `β_min = inf {⟨Kf, f⟩ / ⟨f, f⟩ : f ≠ 0}`,
with `⟨f, g⟩ = ∑ₓ f(x) g(x) π(x)`. -/
def betaMin (K : Matrix V V ℝ) (π : V → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : V → ℝ, f ≠ 0 ∧
    r = MarkovMixing.innerPi π (K.mulVec f) f / MarkovMixing.innerPi π f f}

end

end LogSobolevMC.Metropolis


