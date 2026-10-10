-- Prove2me | Definitions.Def_SinkhornDRO_Duality_Dual
-- name    : SinkhornDRO_Duality_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:22:47.284469+00:00
-- url     : https://prove2.me/theorems/417b61a3-4704-478e-8dd0-cafab204b41a
-- title:
--   Assumption 1, Condition 1, the kernel $\mathbb Q_{x,\epsilon}$, $\bar\rho$, and the dual problem (1)/(Dual)
-- statement:
--   Fix a measurable space $\mathcal Z$, a nominal probability measure $\widehat{\mathbb P}$, a reference measure $\nu$, a cost $c:\mathcal Z\times\mathcal Z\to[0,\infty]$, a parameter $\epsilon>0$, a radius $\rho\in\mathbb R$ and a loss $f:\mathcal Z\to\mathbb R\cup\{\infty\}$.
--
--   **Kernel and constant.** For $x\in\mathcal Z$ the normalizer is $\mathbb E_{u\sim\nu}[e^{-c(x,u)/\epsilon}]$, and the kernel probability distribution (3) is
--
--   $$
--   d\mathbb Q_{x,\epsilon}(z)=\frac{e^{-c(x,z)/\epsilon}}{\mathbb E_{u\sim\nu}[e^{-c(x,u)/\epsilon}]}\,d\nu(z).
--   $$
--
--   The constant (2) is $\bar\rho=\rho+\epsilon\,\mathbb E_{x\sim\widehat{\mathbb P}}\big[\log\mathbb E_{z\sim\nu}[e^{-c(x,z)/\epsilon}]\big]$.
--
--   **Assumption 1 (p. 7).**
--   1. $c$ is measurable and, for $\widehat{\mathbb P}$-almost every $x$, $0\le c(x,z)<\infty$ for $\nu$-almost every $z$;
--   2. $\mathbb E_{z\sim\nu}[e^{-c(x,z)/\epsilon}]<\infty$ for $\widehat{\mathbb P}$-almost every $x$;
--   3. $f$ is measurable with values in $\mathbb R\cup\{\infty\}$;
--   4. every probability measure $\gamma$ on $\mathcal Z\times\mathcal Z$ with first marginal $\widehat{\mathbb P}$ has a regular conditional distribution: $d\gamma(x,z)=d\widehat{\mathbb P}(x)\,d\gamma_x(z)$ for a Markov kernel $x\mapsto\gamma_x$.
--
--   **Dual objective.** For $\lambda>0$ the objective of (Dual) is
--
--   $$
--   \lambda\bar\rho+\lambda\epsilon\,\mathbb E_{x\sim\widehat{\mathbb P}}\Big[\log\mathbb E_{z\sim\mathbb Q_{x,\epsilon}}\big[e^{f(z)/(\lambda\epsilon)}\big]\Big],
--   $$
--
--   and the objective of (1) is $\lambda\rho+\lambda\epsilon\,\mathbb E_{x\sim\widehat{\mathbb P}}\big[\log\mathbb E_{z\sim\nu}[e^{(f(z)-\lambda c(x,z))/(\lambda\epsilon)}]\big]$. By the paper's convention both objectives equal $\operatorname{ess\,sup}_\nu f=\inf\{t:\nu\{f>t\}=0\}$ at $\lambda=0$. The dual value is
--
--   $$
--   V_D=\inf_{\lambda\ge0}\Big\{\lambda\bar\rho+\lambda\epsilon\,\mathbb E_{x\sim\widehat{\mathbb P}}\Big[\log\mathbb E_{z\sim\mathbb Q_{x,\epsilon}}\big[e^{f(z)/(\lambda\epsilon)}\big]\Big]\Big\}.
--   $$
--
--   **Condition 1 (p. 7).** There exists $\lambda>0$ such that $\mathbb E_{z\sim\mathbb Q_{x,\epsilon}}[e^{f(z)/(\lambda\epsilon)}]<\infty$ for $\widehat{\mathbb P}$-almost every $x$. Its **integrated form** asks for some $\lambda>0$ with $\mathbb E_{x\sim\widehat{\mathbb P}}\big[\log\mathbb E_{z\sim\mathbb Q_{x,\epsilon}}[e^{f(z)/(\lambda\epsilon)}]\big]<\infty$, i.e. a finite dual objective at some $\lambda>0$; it implies Condition 1.
--
--   These are the hypotheses and the right-hand side of the strong duality theorem.
--
--   **Formalization Note** The cost takes values in $[0,\infty]$; the weight $e^{-c/\epsilon}$ is $0$ where $c=\infty$. The literal "$\nu\{z:0\le c(x,z)<\infty\}=1$" is read as "$\nu$-almost everywhere", which is what it means for an infinite $\nu$ such as Lebesgue measure. Assumption 1(IV) is stated literally, as a disintegration $\gamma=\widehat{\mathbb P}\otimes\kappa$. The kernel $\mathbb Q_{x,\epsilon}$ is the normalized `withDensity` measure; it is a probability measure whenever the normalizer is finite and positive. $\bar\rho$ is computed with a Bochner integral, and every theorem that uses it assumes that $x\mapsto\log\mathbb E_{\nu}[e^{-c(x,\cdot)/\epsilon}]$ is $\widehat{\mathbb P}$-integrable, so that $\bar\rho$ is the real number of (2). The $\lambda=0$ value is defined as $\operatorname{ess\,sup}_\nu f$ (Mathlib's `essSup`), not as a limit. $e^{(f-\lambda c)/(\lambda\epsilon)}$ is written as $e^{f/(\lambda\epsilon)}\cdot e^{-c/\epsilon}$, with $e^{+\infty}=+\infty$. Expectations are the published extended expectation `DupacovaWets.Consistency.expect` ($\int g^+-\int g^-$ of lower Lebesgue integrals, $+\infty$ when $\int g^+=\infty$). The objectives are defined for every real $\lambda$ but only used on $\lambda\ge0$.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, pp. 6–7, (1), (2), (3), (Dual), Assumption 1, Condition 1

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DupacovaWets.Consistency (expect)

namespace SinkhornDRO.Duality

variable {Z : Type*} [MeasurableSpace Z]

/-- The Gibbs kernel weight `e^{−c(x,z)/ε} ∈ [0, ∞)` (equal to `0` where `c(x,z) = ∞`). -/
noncomputable def kexp (c : Z → Z → ℝ≥0∞) (ε : ℝ) (x z : Z) : ℝ≥0∞ :=
  EReal.exp (((-ε⁻¹ : ℝ) : EReal) * (c x z : EReal))

/-- The normalizing constant `E_{u∼ν}[e^{−c(x,u)/ε}]` of (2)–(3). -/
noncomputable def normalizer (ν : Measure Z) (c : Z → Z → ℝ≥0∞) (ε : ℝ) (x : Z) : ℝ≥0∞ :=
  ∫⁻ u, kexp c ε x u ∂ν

/-- The kernel probability distribution (3), arXiv:2109.11926v5, p. 6:
`dQ_{x,ε}(z) = e^{−c(x,z)/ε} / E_{u∼ν}[e^{−c(x,u)/ε}] dν(z)`.
It is a probability measure whenever the normalizer is finite and positive. -/
noncomputable def Qker (ν : Measure Z) (c : Z → Z → ℝ≥0∞) (ε : ℝ) (x : Z) : Measure Z :=
  (normalizer ν c ε x)⁻¹ • ν.withDensity (kexp c ε x)

/-- The constant (2), arXiv:2109.11926v5, p. 6:
`ρ̄ = ρ + ε E_{x∼P̂}[log E_{z∼ν}[e^{−c(x,z)/ε}]]`. It is used under the hypothesis that
`x ↦ log E_{z∼ν}[e^{−c(x,z)/ε}]` is `P̂`-integrable, which makes `ρ̄` a real number. -/
noncomputable def rhoBar (Phat ν : Measure Z) (c : Z → Z → ℝ≥0∞) (ε ρ : ℝ) : ℝ :=
  ρ + ε * ∫ x, Real.log (normalizer ν c ε x).toReal ∂Phat

/-- Assumption 1, arXiv:2109.11926v5, p. 7, for the nominal distribution `P̂`, the reference
measure `ν`, the cost `c : Z → Z → [0, ∞]`, the regularization `ε` and the loss `f : Z → ℝ ∪ {∞}`.
(I) `c` is measurable and `0 ≤ c(x, z) < ∞` for `ν`-a.e. `z`, for `P̂`-a.e. `x`;
(II) `E_{z∼ν}[e^{−c(x,z)/ε}] < ∞` for `P̂`-a.e. `x`;
(III) `f` is measurable with values in `ℝ ∪ {∞}`;
(IV) every joint distribution `γ` on `Z × Z` with first marginal `P̂` disintegrates as
`dγ(x, z) = dP̂(x) dγ_x(z)` for a Markov kernel `x ↦ γ_x`. -/
structure Assumption1 (Phat ν : Measure Z) (c : Z → Z → ℝ≥0∞) (ε : ℝ) (f : Z → EReal) : Prop where
  cost_measurable : Measurable (Function.uncurry c)
  cost_finite : ∀ᵐ x ∂Phat, ∀ᵐ z ∂ν, c x z ≠ ⊤
  normalizer_finite : ∀ᵐ x ∂Phat, normalizer ν c ε x < ⊤
  loss_measurable : Measurable f
  loss_ne_bot : ∀ z, f z ≠ ⊥
  regular_conditional : ∀ γ : Measure (Z × Z), IsProbabilityMeasure γ → γ.map Prod.fst = Phat →
    ∃ κ : Kernel Z Z, IsMarkovKernel κ ∧ γ = Phat ⊗ₘ κ

/-- `E_{z∼Q_{x,ε}}[e^{f(z)/(λε)}] ∈ [0, ∞]` (with `e^{+∞} = +∞`). -/
noncomputable def dualInner (ν : Measure Z) (c : Z → Z → ℝ≥0∞) (ε : ℝ) (f : Z → EReal) (lam : ℝ)
    (x : Z) : ℝ≥0∞ :=
  ∫⁻ z, EReal.exp ((((lam * ε)⁻¹ : ℝ) : EReal) * f z) ∂(Qker ν c ε x)

/-- The objective of (Dual), arXiv:2109.11926v5, p. 7:
`λρ̄ + λε E_{x∼P̂}[log E_{z∼Q_{x,ε}}[e^{f(z)/(λε)}]]` for `λ > 0`, and, by the paper's convention
(p. 6), the essential supremum `ess sup_ν f` at `λ = 0`. Values in `EReal`. (Only `λ ≥ 0` is
used.) -/
noncomputable def dualObj (Phat ν : Measure Z) (c : Z → Z → ℝ≥0∞) (ε ρ : ℝ) (f : Z → EReal)
    (lam : ℝ) : EReal :=
  if lam = 0 then essSup f ν
  else ((lam * rhoBar Phat ν c ε ρ : ℝ) : EReal) +
    ((lam * ε : ℝ) : EReal) * expect Phat (fun x => ENNReal.log (dualInner ν c ε f lam x))

/-- The objective of (1), arXiv:2109.11926v5, p. 6:
`λρ + λε E_{x∼P̂}[log E_{z∼ν}[e^{(f(z) − λc(x,z))/(λε)}]]` for `λ > 0`, with
`e^{(f − λc)/(λε)}` written as `e^{f/(λε)} · e^{−c/ε}`, and `ess sup_ν f` at `λ = 0`. -/
noncomputable def dualObjNu (Phat ν : Measure Z) (c : Z → Z → ℝ≥0∞) (ε ρ : ℝ) (f : Z → EReal)
    (lam : ℝ) : EReal :=
  if lam = 0 then essSup f ν
  else ((lam * ρ : ℝ) : EReal) +
    ((lam * ε : ℝ) : EReal) * expect Phat (fun x => ENNReal.log
      (∫⁻ z, EReal.exp ((((lam * ε)⁻¹ : ℝ) : EReal) * f z) * kexp c ε x z ∂ν))

/-- The dual optimal value `V_D = inf_{λ ≥ 0} {dual objective}` of (Dual). -/
noncomputable def dualValue (Phat ν : Measure Z) (c : Z → Z → ℝ≥0∞) (ε ρ : ℝ) (f : Z → EReal) :
    EReal :=
  ⨅ lam ∈ Set.Ici (0 : ℝ), dualObj Phat ν c ε ρ f lam

/-- Condition 1, arXiv:2109.11926v5, p. 7: there exists `λ > 0` such that
`E_{z∼Q_{x,ε}}[e^{f(z)/(λε)}] < ∞` for `P̂`-almost every `x`. -/
def Condition1 (Phat ν : Measure Z) (c : Z → Z → ℝ≥0∞) (ε : ℝ) (f : Z → EReal) : Prop :=
  ∃ lam > 0, ∀ᵐ x ∂Phat, dualInner ν c ε f lam x < ⊤

/-- The integrated form of Condition 1: there exists `λ > 0` such that
`E_{x∼P̂}[log E_{z∼Q_{x,ε}}[e^{f(z)/(λε)}]] < ∞`, i.e. the dual objective is finite at some
`λ > 0`. It implies `Condition1`. -/
def Condition1Integrated (Phat ν : Measure Z) (c : Z → Z → ℝ≥0∞) (ε : ℝ) (f : Z → EReal) : Prop :=
  ∃ lam > 0, expect Phat (fun x => ENNReal.log (dualInner ν c ε f lam x)) < ⊤

end SinkhornDRO.Duality


