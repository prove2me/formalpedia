-- Prove2me | Definitions.Def_LogSobolevMC_LowerBound_Setting
-- name    : LogSobolevMC_LowerBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:14.036517+00:00
-- url     : https://prove2.me/theorems/c006dbb4-bda1-4b99-ab4e-00220e0b155b
-- title:
--   Finite-chain ℓᵖ norms, Dirichlet form, spectral gap, log-Sobolev constant, and mixing time
-- statement:
--   For a finite Markov chain with transition matrix $K$ and strictly positive stationary distribution $\pi$, define the bilinear Dirichlet form $\mathcal E(f,g)=\langle(I-K)f,g\rangle_\pi$, the finite-exponent norm $\|f\|_p=(\sum_x|f(x)|^p\pi(x))^{1/p}$, and $\|f\|_\infty=\max_x|f(x)|$. The operator $H_t=e^{-t(I-K)}$ acts on functions by matrix multiplication.
--
--   The quadratic entropy and variational constants are
--
--   $$
--   \mathcal L(f)=\sum_x |f(x)|^2\log\frac{|f(x)|^2}{\|f\|_2^2}\,\pi(x),\qquad
--   \lambda=\inf_{\operatorname{Var}_\pi(f)\ne0}\frac{\mathcal E(f,f)}{\operatorname{Var}_\pi(f)},\qquad
--   \alpha=\inf_{\mathcal L(f)\ne0}\frac{\mathcal E(f,f)}{\mathcal L(f)}.
--   $$
--
--   For Corollary 3.11, $\pi_*=\min_x\pi(x)$ and $\tau$ is the infimum of positive times when every heat-kernel density $H_t(x,y)/\pi(y)$ is within $1/e$ of $1$ in $\ell^2(\pi)$. These objects are shared by every result in this mission.
--
--   **Formalization Note** The infima are real `sInf`s. Under the theorem hypotheses the state space is nonempty; on a singleton, the sets defining $\lambda$ and $\alpha$ are empty and Lean assigns zero. The entropy summand at $f(x)=0$ uses $0\log 0=0$.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), pp. 701–702, 705–706, 714, 728, §2.1–2.3, (2.4), (3.1), Corollary 3.11; https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_mm_spectral
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.LowerBound

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ℓ∞ norm of §2.1. -/
def supNorm (f : V → ℝ) : ℝ :=
  ⨆ x, |f x|

/-- The least stationary mass π_* on a finite state space. -/
def piMin (π : V → ℝ) : ℝ :=
  ⨅ x, π x

/-- The entropy-scale mixing time τ of Corollary 3.11. -/
def tau (K : Matrix V V ℝ) (π : V → ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∀ x : V,
    LogSobolevMC.ChiSquare.lpNorm π 2 (fun y => MarkovMixing.heatKernel K t x y / π y - 1) ≤ Real.exp (-1)}

end

end LogSobolevMC.LowerBound


