-- Prove2me | Definitions.Def_MeanVarASD_AFSD_Defs
-- name    : MeanVarASD_AFSD_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:57.938273+00:00
-- url     : https://prove2.me/theorems/d96363a1-6828-4953-a264-1296302bd6d5
-- title:
--   Definition 1, p. 2, and the proof of Theorem 7, pp. 6–8 — the class U_{γcv,γcx}, (1+γcv,1+γcx)-SD, t, γ*, f, u_U, u_L, B, A, δ*, h
-- statement:
--   The objects of Müller, Scarsini, Tsetlin and Winkler, *Ranking distributions when only means and variances are known*.
--
--   **Utility classes (Definition 1(a)).** For reals $\gamma_{cv},\gamma_{cx}$, the class $\mathcal U_{\gamma_{cv},\gamma_{cx}}$ consists of the continuously differentiable functions $u:\mathbb R\to\mathbb R$ such that
--   $$0\le \gamma_{cv}\,u'(y)\le u'(x)\quad\text{and}\quad 0\le\gamma_{cx}\,u'(x)\le u'(y)\qquad\text{for all } x\le y.$$
--   The parameter $\gamma_{cv}$ bounds how much marginal utility can fall as $x$ decreases, and $\gamma_{cx}$ how much it can fall as $x$ increases; for $\gamma_{cv}=\gamma_{cx}=\gamma\in(0,1]$ every ratio $u'(x)/u'(y)$ of positive marginal utilities lies in $[\gamma,1/\gamma]$.
--
--   **Dominance order (Definition 1(b)).** For $0\le\gamma_{cv},\gamma_{cx}\le1$ and real random variables $X,Y$ on a probability space, $Y$ dominates $X$ by $(1+\gamma_{cv},1+\gamma_{cx})$-SD, written $X\le_{(1+\gamma_{cv},1+\gamma_{cx})}Y$, if
--   $$\mathbb E\,u(Y)\ge\mathbb E\,u(X)\qquad\text{for all } u\in\mathcal U_{\gamma_{cv},\gamma_{cx}}.$$
--   For $\gamma_{cv}=\gamma_{cx}=\gamma$ this is $\varepsilon$-almost first-order stochastic dominance (AFSD) with $\varepsilon=\gamma/(1+\gamma)$; $\gamma=0$ is first-order stochastic dominance and $\gamma=1$ is ranking by means.
--
--   **Constants of Theorem 7 and its proof.** For means $\mu_X,\mu_Y$ and standard deviations $\sigma_X,\sigma_Y$,
--   $$t=\frac{\mu_Y-\mu_X}{\sigma_Y+\sigma_X},\qquad \gamma^*(t)=\frac{1}{1+2t\big(t+\sqrt{t^2+1}\big)},\qquad f(z)=z+\sqrt{1+z^2},$$
--   $$u_U(x;\delta)=\gamma(x-\delta)+(1-\gamma)(x-\delta)_+,\qquad u_L(x;\delta)=\gamma(x-\delta)-(1-\gamma)(\delta-x)_+,$$
--   where $x_+=\max\{x,0\}$,
--   $$B(\gamma,\delta)=\gamma(\mu_X-\delta)+(1-\gamma)\tfrac12\Big(\mu_X-\delta+\sqrt{\sigma_X^2+(\mu_X-\delta)^2}\Big),$$
--   $$A(\gamma,\delta)=\gamma(\mu_Y-\delta)-(1-\gamma)\tfrac12\Big(\delta-\mu_Y+\sqrt{\sigma_Y^2+(\mu_Y-\delta)^2}\Big),$$
--   $$\delta^*=\frac{\mu_X\sigma_Y+\mu_Y\sigma_X}{\sigma_Y+\sigma_X},\qquad h(\delta)=\sigma_Y f\Big(\frac{\delta-\mu_Y}{\sigma_Y}\Big)+\sigma_X f\Big(\frac{\mu_X-\delta}{\sigma_X}\Big).$$
--   In the paper $B$ and $A$ are introduced as the largest value of $\mathbb E\,u_U(X;\delta)$ and the smallest value of $\mathbb E\,u_L(Y;\delta)$ over all laws with the given mean and variance; here they are the closed forms the paper derives for them.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** "Continuously differentiable" is `ContDiff ℝ 1` and $u'$ is `deriv u`. The order requires $0\le\gamma_{cv},\gamma_{cx}\le1$, as Definition 1(b) does, and finite means for $X,Y$, since the identity utility belongs to the class. It compares a utility only when both expected values exist; this prevents Lean's zero value for a non-integrable integral from creating a spurious comparison. The variables live on a probability space. For square-integrable $X,Y$ and $\gamma>0$, every $u$ in the class is Lipschitz, so both expected values exist automatically. Divisions follow Lean's convention $a/0=0$: $t$, $\delta^*$ and $h$ are used only where their denominators are positive, except that the goal theorem evaluates $t$ also when $\sigma_X=\sigma_Y=0$ (then $t=0$ and $\gamma^*=1$; see the goal's note).
-- source:
--   Müller, Scarsini, Tsetlin & Winkler, Ranking distributions when only means and variances are known, INSEAD Working Paper 2020/36/DSC (31 July 2020; SSRN 3440103), p. 2 (PDF 3), Definition 1(a)–(b); p. 4 (PDF 5), notation x₊; p. 6 (PDF 7), Theorem 7 (t, γ*); pp. 7–8 (PDF 8–9), proof of Theorem 7 (u_U, u_L, B, A, f, h, δ*)

import Mathlib

namespace MeanVarASD.AFSD

open MeasureTheory ProbabilityTheory

/-- Definition 1(a), p. 2: the class `U_{γcv,γcx}` of continuously differentiable functions `u`
with `0 ≤ γcv u′(y) ≤ u′(x)` and `0 ≤ γcx u′(x) ≤ u′(y)` for all `x ≤ y`. -/
def UClass (γcv γcx : ℝ) : Set (ℝ → ℝ) :=
  {u | ContDiff ℝ 1 u ∧ ∀ x y : ℝ, x ≤ y →
      0 ≤ γcv * deriv u y ∧ γcv * deriv u y ≤ deriv u x ∧
      0 ≤ γcx * deriv u x ∧ γcx * deriv u x ≤ deriv u y}

/-- Definition 1(b), p. 2: for `0 ≤ γcv, γcx ≤ 1`, `Y` dominates `X` by `(1 + γcv, 1 + γcx)`-SD,
`X ≤_(1+γcv,1+γcx) Y`, if `E u(Y) ≥ E u(X)` for every `u ∈ U_{γcv,γcx}` for which both
expectations exist. The variables have finite means on a probability space. -/
def SDle (γcv γcx : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) : Prop :=
  0 ≤ γcv ∧ γcv ≤ 1 ∧ 0 ≤ γcx ∧ γcx ≤ 1 ∧
  Integrable X P ∧ Integrable Y P ∧
  ∀ u ∈ UClass γcv γcx,
    Integrable (fun ω => u (X ω)) P → Integrable (fun ω => u (Y ω)) P →
      ∫ ω, u (X ω) ∂P ≤ ∫ ω, u (Y ω) ∂P

/-- Theorem 7, p. 6: `t = (µY − µX)/(σY + σX)`. -/
noncomputable def tStat (μX μY σX σY : ℝ) : ℝ := (μY - μX) / (σY + σX)

/-- Theorem 7, p. 6: `γ* = 1/(1 + 2t(t + √(t² + 1)))`. -/
noncomputable def gammaStar (t : ℝ) : ℝ := 1 / (1 + 2 * t * (t + Real.sqrt (t ^ 2 + 1)))

/-- Proof of Theorem 7, p. 7: `f(z) = z + √(1 + z²)`. -/
noncomputable def fAux (z : ℝ) : ℝ := z + Real.sqrt (1 + z ^ 2)

/-- Proof of Theorem 7, p. 7: `u_U(x; δ) = γ(x − δ) + (1 − γ)(x − δ)₊`. -/
noncomputable def uU (γ δ x : ℝ) : ℝ := γ * (x - δ) + (1 - γ) * max (x - δ) 0

/-- Proof of Theorem 7, p. 7: `u_L(x; δ) = γ(x − δ) − (1 − γ)(δ − x)₊`. -/
noncomputable def uL (γ δ x : ℝ) : ℝ := γ * (x - δ) - (1 - γ) * max (δ - x) 0

/-- Proof of Theorem 7, p. 7: `B(γ, δ) = γ(µX − δ) + (1 − γ)½(µX − δ + √(σX² + (µX − δ)²))`. -/
noncomputable def Bval (γ δ μX σX : ℝ) : ℝ :=
  γ * (μX - δ) + (1 - γ) * (1 / 2) * (μX - δ + Real.sqrt (σX ^ 2 + (μX - δ) ^ 2))

/-- Proof of Theorem 7, p. 7: `A(γ, δ) = γ(µY − δ) − (1 − γ)½(δ − µY + √(σY² + (µY − δ)²))`. -/
noncomputable def Aval (γ δ μY σY : ℝ) : ℝ :=
  γ * (μY - δ) - (1 - γ) * (1 / 2) * (δ - μY + Real.sqrt (σY ^ 2 + (μY - δ) ^ 2))

/-- Proof of Theorem 7, p. 8: `δ* = (µX σY + µY σX)/(σY + σX)`. -/
noncomputable def deltaStar (μX μY σX σY : ℝ) : ℝ := (μX * σY + μY * σX) / (σY + σX)

/-- Proof of Theorem 7, p. 7: `h(δ) = σY f((δ − µY)/σY) + σX f((µX − δ)/σX)`
(used only with `σX, σY > 0`). -/
noncomputable def hAux (μX μY σX σY δ : ℝ) : ℝ :=
  σY * fAux ((δ - μY) / σY) + σX * fAux ((μX - δ) / σX)

end MeanVarASD.AFSD


