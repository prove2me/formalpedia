-- Prove2me | Definitions.Def_LogSobolevMC_TwoPoint_Setting
-- name    : LogSobolevMC_TwoPoint_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:56:56.527004+00:00
-- url     : https://prove2.me/theorems/2a00f59d-906d-4755-bccd-f61b6527c941
-- title:
--   §2.1–2.3, §3.1 and Appendix — ℰ(f, g), ‖f‖ₚ, ℒ(f), the spectral gap λ (2.4), the log-Sobolev constant α (3.1), the chain K(x, y) = π(y), π_*, and the functions l(s), e(s)
-- statement:
--   Let $\mathcal X$ be a finite set, $K$ a Markov kernel on $\mathcal X$ (a matrix with $K(x,y)\ge 0$ and $\sum_y K(x,y)=1$) and $\pi$ a probability on $\mathcal X$. This file fixes the objects of Diaconis and Saloff-Coste's Appendix.
--
--   1. The **Dirichlet form** $\mathcal E(f,g)=\langle (I-K)f,g\rangle=\sum_{x}\big(f(x)-Kf(x)\big)g(x)\pi(x)$, where $Kf(x)=\sum_y K(x,y)f(y)$.
--   2. The $\ell^p(\pi)$ **norm** $\|f\|_p=\big(\sum_x |f(x)|^p\pi(x)\big)^{1/p}$, $p\ge1$ real.
--   3. The **entropy functional** $$\mathcal L(f)=\sum_{x\in\mathcal X}|f(x)|^2\log\frac{|f(x)|^2}{\|f\|_2^2}\,\pi(x),$$ with the convention $0\log 0=0$.
--   4. The **spectral gap** $\lambda=\inf\{\mathcal E(f,f)/\mathrm{Var}_\pi(f):\mathrm{Var}_\pi(f)\neq0\}$ of (2.4), where $\mathrm{Var}_\pi(f)=\sum_x (f(x)-E_\pi f)^2\pi(x)$.
--   5. The **log-Sobolev constant** $$\alpha=\inf\Big\{\frac{\mathcal E(f,f)}{\mathcal L(f)}:\mathcal L(f)\neq0\Big\}$$ of (3.1) and (A.2).
--   6. The chain $K(x,y)=\pi(y)$ of the Appendix, which redraws from $\pi$ at every step; $\pi_*=\min_{\mathcal X}\pi$; and the kernel $K(x,y)=1/(|\mathcal X|-1)$ for $x\neq y$, $K(x,x)=0$ of Corollary A.5.
--   7. The two-point chain of Theorem A.2 on $\{0,1\}$ with both rows equal to $(\theta,1-\theta)$, and the measure $\pi(0)=\theta$, $\pi(1)=1-\theta$.
--   8. The functions of the proof of Theorem A.2, $$l(s)=\theta(1+(1-\theta)s)^2\log(1+(1-\theta)s)^2+(1-\theta)(1-\theta s)^2\log(1-\theta s)^2-(1+\theta(1-\theta)s^2)\log(1+\theta(1-\theta)s^2)$$ and $e(s)=\theta(1-\theta)s^2$, which are $\mathcal L$ and $\mathcal E$ of the function with values $1+(1-\theta)s$, $1-\theta s$ on $\{0,1\}$.
--
--   These are the quantities whose exact values the Appendix computes.
--
--   **Formalization Note** Functions on $\mathcal X$ are real-valued; $K$ is a real matrix and $\pi$ a real vector (the stochasticity, invariance and positivity hypotheses are carried by the theorems, using the published `MarkovMixing` predicates). $\lambda$ and $\alpha$ are real `sInf`s over the stated sets, as the page writes "inf" in (3.1) and (A.2); Lean's `sInf` is $0$ on an empty set (one-point $\mathcal X$), and both sets are bounded below by $0$ for a stochastic kernel with invariant $\pi$. $\mathcal E$ is the bilinear form $\langle (I-K)f,g\rangle$ itself, not the symmetrised quadratic form. The `log` in $l(s)$ is the logarithm of the square, $\log\big((1+(1-\theta)s)^2\big)$. $\pi_*$ is the minimum over the nonempty finite set. The spectral gap is the variational one; it is not the eigenvalue-based `MarkovMixing.spectralGap`, which agrees with it only for reversible chains.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 701 (§2.1, norms), p. 705 (§2.3, ℰ), p. 706 (2.4), p. 714 (§3.1, ℒ and (3.1)), pp. 742–744 (Appendix: Theorem A.1, Theorem A.2, l(s), e(s)), p. 747 (Corollary A.5), https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_ChiSquare_Setting
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.TwoPoint

open MarkovMixing
open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The chain `K(x, y) = π(y)` of the Appendix (p. 742): every step is an independent draw from `π`. -/
def indepChain (π : V → ℝ) : Matrix V V ℝ :=
  fun _ y => π y

/-- `π_* = min_𝒳 π` (Theorem A.1, p. 742). -/
def piMin [Nonempty V] (π : V → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty π

/-- The kernel `K(x, y) = 1/(|𝒳| − 1)` for `x ≠ y`, `K(x, x) = 0` of Corollary A.5 (p. 747):
the simple random walk on the complete graph on `𝒳`. -/
def completeChain (V : Type*) [Fintype V] [DecidableEq V] : Matrix V V ℝ :=
  fun x y => if x = y then 0 else 1 / ((Fintype.card V : ℝ) - 1)

end

/-- The chain on `{0, 1}` with matrix `( θ 1 − θ ; θ 1 − θ )` of Theorem A.2 (p. 743). -/
noncomputable def twoPointChain (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![θ, 1 - θ; θ, 1 - θ]

/-- The measure `π(0) = θ`, `π(1) = 1 − θ` on `{0, 1}` (Theorem A.2, p. 743). -/
noncomputable def twoPointPi (θ : ℝ) : Fin 2 → ℝ :=
  ![θ, 1 - θ]

/-- The function `l(s)` of the proof of Theorem A.2 (p. 743): `ℒ` of the function with values
`x = 1 + (1 − θ)s`, `y = 1 − θs` under `π = (θ, 1 − θ)`. -/
noncomputable def lFun (θ s : ℝ) : ℝ :=
  θ * (1 + (1 - θ) * s) ^ 2 * Real.log ((1 + (1 - θ) * s) ^ 2)
    + (1 - θ) * (1 - θ * s) ^ 2 * Real.log ((1 - θ * s) ^ 2)
    - (1 + θ * (1 - θ) * s ^ 2) * Real.log (1 + θ * (1 - θ) * s ^ 2)

/-- The function `e(s) = θ(1 − θ)s²` of the proof of Theorem A.2 (p. 744): `ℰ` of the same function. -/
noncomputable def eFun (θ s : ℝ) : ℝ :=
  θ * (1 - θ) * s ^ 2

end LogSobolevMC.TwoPoint


