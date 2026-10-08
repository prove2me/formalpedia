-- Prove2me | Definitions.Def_SchmidliRuin_Exist_Setting
-- name    : SchmidliRuin_Exist_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:10.204053+00:00
-- url     : https://prove2.me/theorems/b97a2a99-029c-4c3a-8d17-5b093beea480
-- title:
--   §1–§4, pp. 890–899 — standing assumptions, the integral equation (5), condition (6), the function H of (3) and the HJB equation (1)
-- statement:
--   This file fixes the analytic objects of Schmidli's ruin-minimisation problem. Parameters: the premium rate $c>0$, the claim intensity $\lambda>0$, and the drift $\mu>0$ and volatility $\sigma>0$ of the risky asset. The claim sizes $Y$ have law $\nu$ with distribution function $G$, and $c(b)$ is the premium paid for proportional reinsurance with retention level $b\in[0,1]$.
--
--   1. **Reinsurance premium** (p. 891). $c(b)$ is decreasing and continuous on $[0,1]$, $c(1)=0$, and $\liminf_{b\uparrow1}c(b)/(1-b)>0$, written as: there are $\kappa>0$ and $\eta>0$ with $c(b)\ge\kappa(1-b)$ for $b\in(1-\eta,1)$. There is $\underline b\in(0,1]$ with $c(b)>c$ for $0\le b<\underline b$ and $c(b)\le c$ for $\underline b\le b\le1$.
--   2. **Claim law** (p. 890). $\nu$ is a probability measure on $\mathbb R$ with $G(0)=0$ and $G$ continuous. **Bounded density**: $\nu$ has a measurable density $p$ with $0\le p\le C$.
--   3. **Tail.** $\operatorname{tail}(x,b)=\mathbb P[bY>x]$, which is $1-G(x/b)$ for $b\neq0$ and $0$ for $b=0$.
--   4. **The denominator of (5)** (p. 896) and **condition (6)** (p. 899). For $g:\mathbb R\to\mathbb R$ and $x\ge0$,
--   $$
--   D_g(x)=\inf_{b\in[0,1]}\Big[\lambda\Big(1-G(x/b)+\int_0^x\big(1-G((x-z)/b)\big)g(z)\,dz\Big)-\big(c-c(b)\big)g(x)\Big].
--   $$
--   Condition (6) at $u$ is $D_g(u)>0$.
--   5. **Equation (5) on a set $I$.** For every $u\in I$, $g$ is integrable on $[0,u]$, $D_g\neq0$ on $(0,u)$, $1/D_g$ is integrable on $[0,u]$, and
--   $$
--   g(u)=\frac{1}{\dfrac{\mu^2}{2\sigma^2}\displaystyle\int_0^u\frac{dx}{D_g(x)}+\dfrac{c}{\lambda}}.
--   $$
--   6. **Equation (3)** (p. 894). With
--   $$
--   H(u,b)=-\frac{\mu^2f'(u)^2}{2\sigma^2f''(u)}+\big(c-c(b)\big)f'(u)+\lambda\big(\mathbb E[f(u-bY)]-f(u)\big),
--   $$
--   $f$ solves (3) at $u$ when $\sup_{b\in[0,1]}H(u,b)=0$.
--   7. **The HJB equation (1)** (p. 892). $f$ solves (1) at $u$ when
--   $$
--   \sup_{b\in[0,1]}\sup_{A\ge0}\Big[\tfrac12\sigma^2A^2f''(u)+\big(c-c(b)+\mu A\big)f'(u)+\lambda\big(\mathbb E[f(u-bY)]-f(u)\big)\Big]=0 .
--   $$
--   At the boundary $u=0$, with the paper's $f''(0+)=-\infty$ (p. 895), the investment term drops out, and (1) (equivalently (3)) reads $\sup_{b\in[0,1]}\big[(c-c(b))f'(0)+\lambda(\mathbb E[f(-bY)]-f(0))\big]=0$, where $f'(0)$ is the right derivative.
--
--   These are the objects of Theorem 2 and of the lemmas leading to it. Here $f$ plays the role of the (unnormalised) survival probability and $g=f'$.
--
--   **Formalization Note.** Throughout, $f(u)=0$ for $u<0$ is imposed as a hypothesis where needed. Every supremum is encoded as a least upper bound (`IsLUB … 0`), never as Lean's `sSup`, which returns $0$ on unbounded sets. The infimum $D_g$ is Lean's `sInf` over $b\in[0,1]$. It is bounded below whenever $g$ is integrable on $[0,x]$, which the solution predicate requires. The conditions $D_g\neq0$ and $1/D_g$ integrable encode that the integral in (5) exists: Lean's $1/0=0$ would otherwise hide a vanishing denominator. The page notes that the denominator must be strictly positive for $u>0$ (p. 895). The tail helper avoids Lean's $x/0=0$ at $b=0$. $c(b)$ is real-valued, which narrows the model when $\mathbb E[Y]<\infty$: there the paper allows $c(0)=\infty$, and for $\mathbb E[Y]=\infty$ it assumes $c(0)<\infty$ anyway. Stating $\underline b\le1$ is harmless, since $c(1)=0<c$.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), pp. 890–891 (§1, standing assumptions), p. 892 (1), p. 894 (3) and proof of Lemma 3, p. 895, p. 896 (5), p. 899 (6)

import Mathlib
import Definitions.Def_SchmidliRuin_Verif_Setting

namespace SchmidliRuin.Exist

open MeasureTheory ProbabilityTheory Set

/-- "`G(x)` has a bounded density" (Lemmas 4, 5, Theorem 2). -/
def HasBoundedDensity (ν : Measure ℝ) : Prop :=
  ∃ p : ℝ → ℝ, Measurable p ∧ (∃ C : ℝ, ∀ x, 0 ≤ p x ∧ p x ≤ C) ∧
    ν = volume.withDensity (fun x => ENNReal.ofReal (p x))

/-- Condition (6) at `u` (p. 899): the infimum over `b ∈ [0, 1]` (the denominator
`SchmidliRuin.Verif.den` of (5) at `u`) is strictly positive. -/
def Cond6 (c lam : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (g : ℝ → ℝ) (u : ℝ) : Prop :=
  0 < SchmidliRuin.Verif.den c lam cb ν g u

/-- `f` solves (3) at `u` (p. 894): the supremum over `b ∈ [0, 1]` of `H(u, b)` is `0`,
as a least upper bound. -/
def SolvesEq3At (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (f : ℝ → ℝ) (u : ℝ) :
    Prop :=
  IsLUB (SchmidliRuin.Verif.H c lam mu sigma cb ν f u '' Icc 0 1) 0

/-- `f` solves (1), equivalently (3), at the boundary point `u = 0`. With the convention
`f''(0+) = -∞` (p. 895) the investment term drops out (the supremum over `A ≥ 0` is taken at
`A = 0`), and the equation reads
`sup_{b ∈ [0,1]} (c - c(b)) f'(0) + λ(E[f(-bY)] - f(0)) = 0`, with `f'(0)` the right
derivative at `0`. -/
def SolvesHJBAtZero (c lam : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (f : ℝ → ℝ) : Prop :=
  DifferentiableWithinAt ℝ f (Ici 0) 0 ∧
  IsLUB ((fun b => (c - cb b) * derivWithin f (Ici 0) 0 +
    lam * ((∫ y, f (0 - b * y) ∂ν) - f 0)) '' Icc 0 1) 0

end SchmidliRuin.Exist


