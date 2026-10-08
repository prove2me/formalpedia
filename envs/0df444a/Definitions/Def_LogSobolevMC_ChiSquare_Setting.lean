-- Prove2me | Definitions.Def_LogSobolevMC_ChiSquare_Setting
-- name    : LogSobolevMC_ChiSquare_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:00:19.113003+00:00
-- url     : https://prove2.me/theorems/fad963e2-287d-4057-9338-e626432c4d03
-- title:
--   §2.1–2.3, pp. 701–706; §3.1, p. 714; p. 721 — ℓᵖ(π) norms, ℰ(f, g) = ⟨(I − K)f, g⟩, ℒ(f), ℒ_p(f), the spectral gap λ (2.4), the log-Sobolev constant α (3.1), H_t f and h_t^x
-- statement:
--   Let $\mathcal X$ be a finite set, $K$ a Markov kernel on $\mathcal X$ (nonnegative entries, rows summing to $1$) and $\pi$ a probability on $\mathcal X$, invariant for $K$ and charging every point. Write $Kf(x)=\sum_y K(x,y)f(y)$, $E_\pi f=\sum_x f(x)\pi(x)$, $\operatorname{Var}_\pi(f)=\|f-E_\pi f\|_2^2$ and $\langle f,g\rangle=\sum_x f(x)g(x)\pi(x)$. This file fixes the objects of Sections 2 and 3 of Diaconis and Saloff-Coste shared by every mission of the series.
--
--   1. The **$\ell^p(\pi)$ norm**, for real $p\ge1$:
--   $$\|f\|_p=\Big(\sum_x |f(x)|^p\pi(x)\Big)^{1/p}.$$
--   2. The **Dirichlet form** $\mathcal E(f,g)=\langle (I-K)f,g\rangle=\sum_x\big(f(x)-Kf(x)\big)g(x)\pi(x)$. It is bilinear, and symmetric only when $(K,\pi)$ is reversible.
--   3. The **entropy-like functionals**
--   $$\mathcal L(f)=\sum_x |f(x)|^2\log\frac{|f(x)|^2}{\|f\|_2^2}\,\pi(x),\qquad
--   \mathcal L_p(f)=\sum_x |f(x)|^p\log\frac{|f(x)|^p}{\|f\|_p^p}\,\pi(x).$$
--   4. The **spectral gap** (2.4) and the **log-Sobolev constant** (3.1):
--   $$\lambda=\min\Big\{\frac{\mathcal E(f,f)}{\operatorname{Var}_\pi(f)}:\operatorname{Var}_\pi(f)\ne0\Big\},\qquad
--   \alpha=\inf\Big\{\frac{\mathcal E(f,f)}{\mathcal L(f)}:\mathcal L(f)\ne0\Big\}.$$
--   5. The **heat semigroup** $H_t=e^{-t(I-K)}=e^{-t}\sum_{n\ge0}\frac{t^n}{n!}K^n$ acting on functions, $H_tf(x)=\sum_y H_t(x,y)f(y)$, and the **density** $h_t^x(y)=H_t(x,y)/\pi(y)$ of the measure $H_t^x=H_t(x,\cdot)$ with respect to $\pi$.
--
--   These are the objects in which the chi-square, entropy, hypercontractivity and comparison results of the paper are stated.
--
--   **Formalization Note** $K$ is a real matrix, $H_t$ is the published `MarkovMixing.heatKernel K t`, and $\operatorname{Var}_\pi$ is the published `MarkovMixing.distVar`. The definitions are total: the standing hypotheses (stochastic $K$, invariant $\pi$ with $\pi(x)>0$, irreducibility in Section 3) are binders of each theorem. $\lambda$ and $\alpha$ are real infima (`sInf`): under the standing hypotheses both sets are bounded below by $0$, and both are empty exactly when $|\mathcal X|=1$, in which case Lean returns $0$; the minimum in (2.4) is not asserted to be attained. $\lambda$ is the variational quantity of (2.4), not an eigenvalue, so it is the paper's $\lambda$ also for nonreversible chains. `Real.log 0 = 0` gives the convention $0\log 0=0$ in $\mathcal L$ and $\mathcal L_p$. The norm uses the real power `Real.rpow`; $\|f\|_\infty$ is not part of this file.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), pp. 701–702, §2.1 (norms, H_t, h_t^x); p. 705, §2.3 (ℰ); p. 706, (2.4); p. 714, §3.1, (3.1); p. 721, proof of Theorem 3.5 (ℒ_p); https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_mm_continuous

namespace LogSobolevMC.ChiSquare

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Dirichlet form `ℰ(f, g) = ⟨(I − K)f, g⟩ = Σ_x (f(x) − Kf(x)) g(x) π(x)` (§2.3, p. 705).
Bilinear, not symmetric for nonreversible `K`; the order of the arguments is the paper's. -/
def dirichlet (K : Matrix V V ℝ) (π : V → ℝ) (f g : V → ℝ) : ℝ :=
  ∑ x, (f x - K.mulVec f x) * g x * π x

/-- The norm `‖f‖_p = (Σ_x |f(x)|^p π(x))^{1/p}` of `ℓᵖ(π)`, for a real exponent `p`
(§2.1, p. 701; the paper uses `1 ≤ p`). -/
def lpNorm (π : V → ℝ) (p : ℝ) (f : V → ℝ) : ℝ :=
  (∑ x, |f x| ^ p * π x) ^ (1 / p)

/-- `ℒ(f) = Σ_x |f(x)|² log(|f(x)|² / ‖f‖₂²) π(x)` (§3.1, p. 714). With `Real.log 0 = 0`, the
terms with `f(x) = 0` vanish (the convention `0 log 0 = 0`). -/
def entL (π : V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ x, |f x| ^ (2 : ℝ) * Real.log (|f x| ^ (2 : ℝ) / lpNorm π 2 f ^ (2 : ℝ)) * π x

/-- `ℒ_p(f) = Σ_x |f(x)|^p log(|f(x)|^p / ‖f‖_p^p) π(x)` (proof of Theorem 3.5, p. 721). -/
def entLp (π : V → ℝ) (p : ℝ) (f : V → ℝ) : ℝ :=
  ∑ x, |f x| ^ p * Real.log (|f x| ^ p / lpNorm π p f ^ p) * π x

/-- The spectral gap `λ = min {ℰ(f, f)/Var(f) : Var(f) ≠ 0}` of (2.4), p. 706, as a real `sInf`;
variational, so it is the paper's `λ` also for nonreversible chains. -/
def gap (K : Matrix V V ℝ) (π : V → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : V → ℝ,
    MarkovMixing.distVar π f ≠ 0 ∧ r = dirichlet K π f f / MarkovMixing.distVar π f}

/-- The log-Sobolev constant `α = inf {ℰ(f, f)/ℒ(f) : ℒ(f) ≠ 0}` of (3.1), p. 714, as a real `sInf`. -/
def logSobolev (K : Matrix V V ℝ) (π : V → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : V → ℝ, entL π f ≠ 0 ∧ r = dirichlet K π f f / entL π f}

/-- `H_t = e^{−t(I−K)}` acting on a function, `H_t f(x) = Σ_y H_t(x, y) f(y)` (§2.1, p. 702). -/
def heatOp (K : Matrix V V ℝ) (t : ℝ) (f : V → ℝ) : V → ℝ :=
  (MarkovMixing.heatKernel K t).mulVec f

/-- The density `h_t^x(y) = H_t(x, y)/π(y)` of `H_t^x` with respect to `π` (§2.1, p. 702). -/
def density (K : Matrix V V ℝ) (π : V → ℝ) (t : ℝ) (x : V) : V → ℝ :=
  fun y => MarkovMixing.heatKernel K t x y / π y

end

end LogSobolevMC.ChiSquare


