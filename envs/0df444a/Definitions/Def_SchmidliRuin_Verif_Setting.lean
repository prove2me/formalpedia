-- Prove2me | Definitions.Def_SchmidliRuin_Verif_Setting
-- name    : SchmidliRuin_Verif_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:29.505801+00:00
-- url     : https://prove2.me/theorems/0822eb2b-c4a8-4794-9f7e-bd227c07b16c
-- title:
--   §1–§2, pp. 891–896 — premium condition on c(b), claim law, HJB equation (1), A* of (2), H of (3), maximiser b*, equation (5)
-- statement:
--   This file collects the analytic objects of H. Schmidli's paper *On minimizing the ruin probability by investment and reinsurance* (2002). Throughout, $c>0$ is the premium rate, $\lambda>0$ the claim intensity, $\mu,\sigma>0$ the drift and volatility of the risky asset, and $\nu$ the claim-size law with distribution function $G$.
--
--   1. **Reinsurance premium** (p. 891). A function $c(b)$, $b\in[0,1]$, is an admissible reinsurance premium if it is decreasing and continuous on $[0,1]$, $c(1)=0$, $\liminf_{b\uparrow1}c(b)/(1-b)>0$, and there is $\underline b\in(0,1]$ with $c(b)>c$ for $b<\underline b$ and $c(b)\le c$ for $b\ge\underline b$.
--   2. **Claim law** (p. 890). $\nu$ is a probability measure on $\mathbb R$ with $G(0)=0$ and $G$ continuous.
--   3. **Tail.** $\operatorname{tail}(x,b)=\mathbb P[bY>x]$, i.e. $1-G(x/b)$ for $b\ne0$ and $0$ for $b=0$.
--   4. **HJB equation (1)** (p. 892). $f$ solves (1) at $u$ if
--   $$\sup_{b\in[0,1]}\sup_{A\ge0}\Big[\tfrac12\sigma^2A^2f''(u)+(c-c(b)+\mu A)f'(u)+\lambda\big(\mathbb E[f(u-bY)]-f(u)\big)\Big]=0,$$
--   meaning that the set of bracket values has least upper bound $0$.
--   5. **$H$ and $A^*$** (p. 894). $H(u,b)=-\frac{\mu^2f'(u)^2}{2\sigma^2f''(u)}+(c-c(b))f'(u)+\lambda(\mathbb E[f(u-bY)]-f(u))$ is the bracket of (3), and $A^*(x)=-\mu f'(x)/(\sigma^2f''(x))$ is the optimal investment (2).
--   6. **Maximiser $b^*$.** A measurable $b^*:\mathbb R\to[0,1]$ such that for every $x>0$, $b^*(x)$ maximises $b\mapsto(c-c(b))f'(x)+\lambda(\mathbb E[f(x-bY)]-f(x))$ over $[0,1]$.
--   7. **Equation (5)** (p. 896). With
--   $$\operatorname{den}_g(x)=\inf_{b\in[0,1]}\lambda\Big(1-G(x/b)+\int_0^x\big(1-G((x-z)/b)\big)g(z)\,dz\Big)-(c-c(b))g(x),$$
--   $g$ solves (5) on $I$ if for every $u\in I$: $g$ is integrable on $[0,u]$, $\operatorname{den}_g\ne0$ on $(0,u)$, $1/\operatorname{den}_g$ is integrable on $[0,u]$, and
--   $$g(u)=\frac{1}{\frac{\mu^2}{2\sigma^2}\int_0^u\frac{dx}{\operatorname{den}_g(x)}+\frac c\lambda}.$$
--   8. **Hypotheses of Theorem 1.** $f=0$ on $(-\infty,0)$, $f\ge0$, strictly increasing and continuous on $[0,\infty)$, $C^2$ on $(0,\infty)$, solving (1) at every $u>0$.
--
--   These are the analytic ingredients of the verification theorem: the HJB equation characterises the maximal survival probability, and (5) is the integral equation for $g=f'$.
--
--   **Formalization Note** The supremum in (1) is stated with `IsLUB`, so a family that is unbounded above (for instance when $f''(u)>0$) never counts as a solution. The premium $c(b)$ is real valued, which also forces $c(0)<\infty$; the paper allows $c(0)=\infty$ when $\mathbb E[Y]<\infty$, so the model is slightly narrower there. The liminf condition is written as: $c(b)\ge\kappa(1-b)$ near $1$ for some $\kappa>0$, which is equivalent (including the value $+\infty$). `tail` takes the value $0$ at $b=0$ because Lean's $x/0=0$ would give $1-G(0)=1$. The convention $f(u)=0$ for $u<0$ is a separate hypothesis on $f$. "Twice continuously differentiable" is read on $(0,\infty)$, because the paper's solutions have $f''(0+)=-\infty$ (p. 895). The three integrability and non-vanishing clauses of (5) say that the integral in (5) exists, which the paper takes for granted ("the denominator must be strictly positive for $u>0$", p. 895).
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), pp. 890–891 (§1, assumptions on G and c(b)), p. 892 (1), p. 894 (2), (3), proof of Lemma 3 (H), p. 896 (5) and Theorem 1

import Mathlib

open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace SchmidliRuin.Verif

/-- The standing assumption of Schmidli (2002), p. 891, on the reinsurance premium rate
`c(b)`, `b ∈ [0, 1]`, given the premium rate `c` of the insurer: `c(b)` is decreasing
(non-increasing) and continuous on `[0, 1]`, `c(1) = 0`,
`liminf_{b ↑ 1} c(b)/(1 - b) > 0` (written as: `c(b) ≥ κ (1 - b)` for some `κ > 0` and all
`b` in a left neighbourhood of `1`), and there is `b̲ > 0` with `c(b) > c` for `b < b̲` and
`c(b) ≤ c` for `b ≥ b̲` (`b̲ ≤ 1` follows from `c(1) = 0 < c`). The rate is real valued, so
`c(0) < ∞`. -/
def ReinsPremium (c : ℝ) (cb : ℝ → ℝ) : Prop :=
  AntitoneOn cb (Icc 0 1) ∧
  ContinuousOn cb (Icc 0 1) ∧
  cb 1 = 0 ∧
  (∃ κ > 0, ∃ η > 0, ∀ b ∈ Ioo (1 - η) 1, κ * (1 - b) ≤ cb b) ∧
  ∃ bl : ℝ, 0 < bl ∧ bl ≤ 1 ∧ (∀ b ∈ Ico 0 bl, c < cb b) ∧ (∀ b ∈ Icc bl 1, cb b ≤ c)

/-- The claim-size law of p. 890: a probability measure `ν` on `ℝ` whose distribution
function `G = cdf ν` satisfies `G(0) = 0` (claims are positive) and is continuous. -/
def ClaimLaw (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ν (Iic 0) = 0 ∧ Continuous (cdf ν)

/-- `tail ν x b = ℙ[b Y > x]` for `x ≥ 0`, i.e. the paper's `1 - G(x/b)`, with the value `0` at
`b = 0` (Lean's `x / 0 = 0` would otherwise give `1 - G(0) = 1`). -/
noncomputable def tail (ν : Measure ℝ) (x b : ℝ) : ℝ :=
  if b = 0 then 0 else 1 - cdf ν (x / b)

/-- The bracket of the Hamilton–Jacobi–Bellman equation (1), p. 892, at capital `u`, retention
`b` and investment `A`:
`½σ²A² f''(u) + (c - c(b) + µA) f'(u) + λ(𝔼[f(u - bY)] - f(u))`, `Y ∼ ν`. -/
noncomputable def hjbTerm (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (f : ℝ → ℝ)
    (u b A : ℝ) : ℝ :=
  1 / 2 * sigma ^ 2 * A ^ 2 * deriv (deriv f) u + (c - cb b + mu * A) * deriv f u
    + lam * ((∫ y, f (u - b * y) ∂ν) - f u)

/-- `f` solves the HJB equation (1) at `u`: the set of values of the bracket over
`b ∈ [0, 1]`, `A ≥ 0` has least upper bound `0` (so the supremum is finite and equals `0`).
The paper's convention `f(x) = 0` for `x < 0` is imposed separately as a hypothesis. -/
def SolvesHJB (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (f : ℝ → ℝ) (u : ℝ) : Prop :=
  IsLUB {v | ∃ b ∈ Icc (0 : ℝ) 1, ∃ A : ℝ, 0 ≤ A ∧ v = hjbTerm c lam mu sigma cb ν f u b A} 0

/-- The function `H(u, b)` of the proof of Lemma 3, p. 894 (the bracket of (3)):
`-µ² f'(u)² / (2σ² f''(u)) + (c - c(b)) f'(u) + λ(𝔼[f(u - bY)] - f(u))`. -/
noncomputable def H (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (f : ℝ → ℝ)
    (u b : ℝ) : ℝ :=
  -(mu ^ 2 * deriv f u ^ 2) / (2 * sigma ^ 2 * deriv (deriv f) u) + (c - cb b) * deriv f u
    + lam * ((∫ y, f (u - b * y) ∂ν) - f u)

/-- The optimal investment (2), p. 894: `A*(x) = -µ f'(x) / (σ² f''(x))`. -/
noncomputable def Astar (mu sigma : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(mu * deriv f x) / (sigma ^ 2 * deriv (deriv f) x)

/-- The part of the HJB bracket that depends on the retention `b`:
`(c - c(b)) f'(x) + λ(𝔼[f(x - bY)] - f(x))`. -/
noncomputable def retentionTerm (c lam : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (f : ℝ → ℝ)
    (x b : ℝ) : ℝ :=
  (c - cb b) * deriv f x + lam * ((∫ y, f (x - b * y) ∂ν) - f x)

/-- `bstar` is a measurable choice of the maximiser `b*(x)` of the left-hand side of the HJB
equation over `b ∈ [0, 1]`, for every `x > 0` (p. 894: "the argument `b*(u)` (not necessarily
unique) for which the supremum is taken exists and … can be chosen to be measurable"). -/
def IsBStar (c lam : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (f : ℝ → ℝ) (bstar : ℝ → ℝ) : Prop :=
  Measurable bstar ∧ (∀ x, bstar x ∈ Icc (0 : ℝ) 1) ∧
  ∀ x > 0, IsMaxOn (retentionTerm c lam cb ν f x) (Icc 0 1) (bstar x)

/-- The denominator of equation (5), p. 896, at `x`:
`inf_{b ∈ [0,1]} λ(1 - G(x/b) + ∫_0^x (1 - G((x - z)/b)) g(z) dz) - (c - c(b)) g(x)`. -/
noncomputable def den (c lam : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  sInf ((fun b => lam * (tail ν x b + ∫ z in (0 : ℝ)..x, tail ν (x - z) b * g z)
    - (c - cb b) * g x) '' Icc 0 1)

/-- `g` solves equation (5), p. 896, on the set `I ⊆ [0, ∞)`: for every `u ∈ I`, `g` is
integrable on `[0, u]`, the denominator of (5) does not vanish on `(0, u)`, its reciprocal is
integrable on `[0, u]`, and
`g(u) = 1 / ((µ²/(2σ²)) ∫_0^u den(x)⁻¹ dx + c/λ)`. -/
def SolvesEq5On (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (g : ℝ → ℝ)
    (I : Set ℝ) : Prop :=
  ∀ u ∈ I,
    IntervalIntegrable g volume 0 u ∧
    (∀ x ∈ Ioo 0 u, den c lam cb ν g x ≠ 0) ∧
    IntervalIntegrable (fun x => (den c lam cb ν g x)⁻¹) volume 0 u ∧
    g u = 1 / (mu ^ 2 / (2 * sigma ^ 2) * (∫ x in (0 : ℝ)..u, (den c lam cb ν g x)⁻¹)
      + c / lam)

/-- The analytic hypotheses of Theorem 1, p. 896, on `f : ℝ → ℝ`: the convention `f = 0` on
`(-∞, 0)`, `f ≥ 0` on `[0, ∞)`, `f` strictly increasing and continuous on `[0, ∞)`, twice
continuously differentiable on `(0, ∞)`, and solving the HJB equation (1) at every `u > 0`. -/
def IsHJBSolution (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ x < 0, f x = 0) ∧ (∀ x, 0 ≤ x → 0 ≤ f x) ∧ StrictMonoOn f (Ici 0) ∧
  ContinuousOn f (Ici 0) ∧ ContDiffOn ℝ 2 f (Ioi 0) ∧
  ∀ u > 0, SolvesHJB c lam mu sigma cb ν f u

end SchmidliRuin.Verif


