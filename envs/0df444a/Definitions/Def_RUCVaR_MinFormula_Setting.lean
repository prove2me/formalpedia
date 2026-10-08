-- Prove2me | Definitions.Def_RUCVaR_MinFormula_Setting
-- name    : RUCVaR_MinFormula_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:24.798662+00:00
-- url     : https://prove2.me/theorems/7f9165f4-c476-4319-a0ed-d76208b9d7b5
-- title:
--   §2–§3, pp. 5–14 — Ψ (1), Ψ(x, α⁻) (2), VaR⁺ (6), the β-tail distribution (8), CVaR (7), CVaR⁺ (10), λ_β (20), F_β (27)
-- statement:
--   The objects of Rockafellar and Uryasev's analysis of conditional value-at-risk for a general (possibly discrete) loss distribution.
--
--   Let $P$ be a Borel probability measure on $\mathbb R^m$, the law of a random vector $y$, and let $f(x,y)$ be the loss associated with a decision $x\in\mathbb R^n$ and the outcome $y$. Fix a confidence level $\beta$.
--
--   1. **Distribution function of the loss**, (1) and (2): $\Psi(x,\alpha)=P\{y \mid f(x,y)\le\alpha\}$ and its left limit $\Psi(x,\alpha^-)=P\{y\mid f(x,y)<\alpha\}$.
--   2. **β-VaR**, Definition 1, (4): $\alpha_\beta(x)=\min\{\alpha\mid \Psi(x,\alpha)\ge\beta\}$. This is the published value-at-risk $\inf\{\alpha \mid P\{f(x,\cdot)\le\alpha\}\ge\beta\}$ applied to the loss $f(x,\cdot)$; $\mathrm{VaR}$ here is only an abbreviation of it.
--   3. **Upper β-VaR**, Definition 2, (6): $\alpha^+_\beta(x)=\inf\{\alpha\mid \Psi(x,\alpha)>\beta\}$.
--   4. **β-tail distribution function**, (8):
--   $$
--   \Psi_\beta(x,\alpha)=\begin{cases}0 & \alpha<\alpha_\beta(x),\\[2pt] \dfrac{\Psi(x,\alpha)-\beta}{1-\beta} & \alpha\ge\alpha_\beta(x).\end{cases}
--   $$
--      A probability measure $\mu$ on $\mathbb R$ is *a β-tail distribution* when $\mu((-\infty,a])=\Psi_\beta(x,a)$ for every $a$. Since a probability measure on $\mathbb R$ is determined by its distribution function, there is at most one; *the* β-tail distribution is that measure (and the zero measure if none exists).
--   5. **β-CVaR**, Definition 3, (7): $\phi_\beta(x)$ is the mean $\int z\,d\mu(z)$ of the β-tail distribution $\mu$.
--   6. **Upper β-CVaR**, Definition 4, (10): $\phi^+_\beta(x)=E\{f(x,y)\mid f(x,y)>\alpha_\beta(x)\}$, the integral of $f(x,\cdot)$ over $\{f(x,\cdot)>\alpha_\beta(x)\}$ divided by the probability of that event. It is meaningful only when $\Psi(x,\alpha_\beta(x))<1$.
--   7. **Weight of the VaR atom**, (20): $\lambda_\beta(x)=[\Psi(x,\alpha_\beta(x))-\beta]/[1-\beta]$.
--   8. **The function $F_\beta$**, (27):
--   $$
--   F_\beta(x,\alpha)=\alpha+\frac{1}{1-\beta}\,E\big\{[f(x,y)-\alpha]^+\big\},\qquad [t]^+=\max\{0,t\}.
--   $$
--
--   The paper's central result (Theorem 10) is that $\phi_\beta(x)=\min_\alpha F_\beta(x,\alpha)$; here $\phi_\beta$ is deliberately defined as the mean of the tail distribution and not through $F_\beta$, so that this identity has content.
--
--   **Formalization Note** The outcome space is $\mathbb R^m$ (`Fin m → ℝ`) with its Borel σ-algebra; the paper's support set $Y\subseteq\mathbb R^m$ is not modelled, since a law on $Y$ is a law on $\mathbb R^m$ concentrated on $Y$ and nothing in §2–§3 uses $Y$ itself. Probabilities are real numbers (`P.real`). VaR is the published `MultistageStochastic.valueAtRisk` (a real `sInf`), referenced, not redefined. VaR, VaR⁺ and CVaR⁺ are real infima or quotients, so they carry their intended meaning only under the hypotheses the theorems state ($P$ a probability measure, $0<\beta<1$, and $\Psi(x,\alpha_\beta(x))<1$ for CVaR⁺).
-- source:
--   Rockafellar & Uryasev, Conditional value-at-risk for general loss distributions, Research Report #2001-5, Univ. of Florida, April 4, 2001, pp. 5–14, (1), (2), Definitions 1–4, (6)–(8), (10), (20), (27)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional

namespace RUCVaR.MinFormula

open MeasureTheory

/-- Rockafellar–Uryasev, Research Report #2001-5, §2, p. 5, (1): the distribution function of the
loss `z = f(x, y)`, `Ψ(x, α) = P{y | f(x, y) ≤ α}`. -/
noncomputable def Psi {m n : ℕ} (P : Measure (Fin m → ℝ)) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (x : Fin n → ℝ) (α : ℝ) : ℝ :=
  P.real {y | f x y ≤ α}

/-- §2, p. 5, (2): the left limit `Ψ(x, α⁻) = P{y | f(x, y) < α}`, as the page defines it. -/
noncomputable def PsiLeft {m n : ℕ} (P : Measure (Fin m → ℝ)) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (x : Fin n → ℝ) (α : ℝ) : ℝ :=
  P.real {y | f x y < α}

/-- Definition 1, p. 5, (4): the β-VaR `α_β(x) = min{α | Ψ(x, α) ≥ β}`. A transparent abbreviation of
the published `MultistageStochastic.valueAtRisk` applied to the loss `f x`. -/
noncomputable abbrev VaR {m n : ℕ} (P : Measure (Fin m → ℝ)) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  MultistageStochastic.valueAtRisk P (f x) β

/-- Definition 2, p. 7, (6): the upper β-VaR `α⁺_β(x) = inf{α | Ψ(x, α) > β}`. -/
noncomputable def VaRPlus {m n : ℕ} (P : Measure (Fin m → ℝ)) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  sInf {α : ℝ | β < Psi P f x α}

/-- Definition 3, p. 7, (8): the β-tail distribution function
`Ψ_β(x, α) = 0` for `α < α_β(x)` and `[Ψ(x, α) − β]/[1 − β]` for `α ≥ α_β(x)`. -/
noncomputable def PsiBeta {m n : ℕ} (P : Measure (Fin m → ℝ)) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (x : Fin n → ℝ) (α : ℝ) : ℝ :=
  if α < VaR P f β x then 0 else (Psi P f x α - β) / (1 - β)

/-- Definition 3, p. 7: `μ` is a β-tail distribution of the loss, i.e. a probability measure on `ℝ`
whose distribution function is `Ψ_β(x, ·)` of (8). -/
def IsBetaTailDistribution {m n : ℕ} (P : Measure (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (x : Fin n → ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ a : ℝ, μ.real (Set.Iic a) = PsiBeta P f β x a

/-- Definition 3, p. 7: *the* β-tail distribution (a probability measure is determined by its
distribution function, so the choice is unique when one exists; `0` otherwise). -/
noncomputable def tailDist {m n : ℕ} (P : Measure (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (x : Fin n → ℝ) : Measure ℝ := by
  classical
  exact if h : ∃ μ, IsBetaTailDistribution P f β x μ then h.choose else 0

/-- Definition 3, p. 7, (7): the β-CVaR `φ_β(x)`, the mean of the β-tail distribution. -/
noncomputable def CVaR {m n : ℕ} (P : Measure (Fin m → ℝ)) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ z, z ∂(tailDist P f β x)

/-- Definition 4, p. 8, (10): the upper β-CVaR `φ⁺_β(x) = E{f(x, y) | f(x, y) > α_β(x)}`, the
elementary conditional expectation. Meaningful only when `Ψ(x, α_β(x)) < 1` (p. 9). -/
noncomputable def CVaRPlus {m n : ℕ} (P : Measure (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∫ y in {y | VaR P f β x < f x y}, f x y ∂P) / P.real {y | VaR P f β x < f x y}

/-- Proposition 6, p. 10, (20): `λ_β(x) = [Ψ(x, α_β(x)) − β]/[1 − β]`. -/
noncomputable def lambdaBeta {m n : ℕ} (P : Measure (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  (Psi P f x (VaR P f β x) - β) / (1 - β)

/-- §3, p. 14, (27): `F_β(x, α) = α + (1/(1 − β)) E{[f(x, y) − α]⁺}`. -/
noncomputable def Fbeta {m n : ℕ} (P : Measure (Fin m → ℝ)) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (x : Fin n → ℝ) (α : ℝ) : ℝ :=
  α + (1 - β)⁻¹ * ∫ y, max (f x y - α) 0 ∂P

end RUCVaR.MinFormula


