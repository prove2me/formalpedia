-- Prove2me | Definitions.Def_AccelScal_UCMonopoly_Setting
-- name    : AccelScal_UCMonopoly_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:56.963978+00:00
-- url     : https://prove2.me/theorems/76a8d1d0-3ebf-4fd0-b33e-c1e486ddb5b7
-- title:
--   §2, (2), (4), (7), (A.1), pp. 3–5, 18 — power-form R&D technology, the unconstrained monopoly's R&D value under an exponential discovery time, and its set of optimal intensities
-- statement:
--   This file sets up the model of an unconstrained (UC) monopoly firm choosing an R&D investment intensity.
--
--   **Technology (2).** A technology is a tuple $T=(A,\beta,\eta,\gamma)$ of real numbers. The expected project payoff and the discovery intensity at investment intensity $R$ are
--   $$u(R)=A\,R^{\beta},\qquad \lambda(R)=\eta\,R^{\gamma}.$$
--   The **standing assumptions** are those of (2), $A>0$, $\eta>0$, $\beta,\gamma\in[0,1)$, $\beta+\gamma<1$, together with $A\eta>1$ (investment takes place). A project is *scalable* if $u'>0$ (here: $\beta>0$) and *accelerable* if $\lambda'>0$ (here: $\gamma>0$).
--
--   **Range (7).** The investment intensity ranges over $[\underline R,\bar R]=[1,\bar R]$ with
--   $$\bar R=(A\eta)^{1/(1-(\beta+\gamma))}.$$
--
--   **R&D value (4).** Fix a discount rate $r$. The discovery time $\tau_d$ is exponentially distributed with rate $\lambda(R)$. The firm pays $R$ per unit of time until $\tau_d$ and then receives $u(R)$; the R&D value of intensity $R$ is
--   $$\Pi(R)=\mathbb E\Big[e^{-r\tau_d}\,u(R)-R\int_0^{\tau_d}e^{-rt}\,dt\Big],\qquad \tau_d\sim\mathrm{Exp}(\lambda(R)).$$
--
--   **Optimal intensities.** $R^*_{uc}$ is the *set* of maximizers of $\Pi$ over $[1,\bar R]$:
--   $$R^*_{uc}=\{R\in[1,\bar R]:\ \Pi(R')\le\Pi(R)\ \text{for all }R'\in[1,\bar R]\}.$$
--
--   **Log value (A.1).** $\ln V(R)=\ln(u(R)\lambda(R)-R)-\ln(\lambda(R)+r)$, the logarithm of the closed form (5) of the project value.
--
--   **Ordering of optimal sets.** For sets $S,S'$ of intensities, "$S'$ lies above $S$" means: every $x\in S$ and every $y\in S'$ satisfy $x\le y$, and $x<y$ whenever $x>\underline R=1$. This is how the paper's derivative claims $\partial R^*_{uc}/\partial s>0$ are posed.
--
--   These objects are the vocabulary of Proposition 1 (p. 5) and of the cross-partial identities (A.2)–(A.4) and (A.6) of its proof (Appendix A.2, p. 18). The ordering of optimal sets is also how the best-response claims of Proposition 3 (p. 8) are posed.
--
--   **Formalization Note** The random payoff $\tilde u(R)$ is replaced by its mean $u(R)$, the only property the proofs use, and the cash-flow term of (4) is dropped because it does not depend on $R$. The value is defined as the expectation (4), not by its closed form (5), so that Lemma 1 has content. The powers $R^{\beta}$, $R^{\gamma}$ are real powers (`Real.rpow`); all theorems take $R\ge1$ or $R>0$. The expectation is taken under Mathlib's exponential law `expMeasure`, which is the zero measure for a non-positive rate; every theorem has $\eta>0$ and $R>0$, so the rate $\lambda(R)$ is positive. The logarithm $\ln V$ is meaningful only where $u\lambda>R$, i.e. $R<\bar R$; the theorems that use it assume this. Optimal intensities are a set, never a selected optimum. The condition $A\eta>1$ is an addition (the paper's "conditional on investment taking place", p. 5).
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, pp. 3–5, (2), (4), (7); p. 18, (A.1)

import Mathlib

namespace AccelScal.UCMonopoly

/-- Technology parameters of the R&D project, (2): `u(R) = A R^β`, `λ(R) = η R^γ`. -/
structure Tech where
  A : ℝ
  β : ℝ
  η : ℝ
  γ : ℝ

namespace Tech

/-- Standing assumptions: (2) (`A > 0`, `η > 0`, `β, γ ∈ [0,1)`, `β + γ < 1`) and the disclosed
condition `A η > 1` (investment takes place: the project value at `R̲ = 1` is positive). -/
def Standing (T : Tech) : Prop :=
  0 < T.A ∧ 0 < T.η ∧ 0 ≤ T.β ∧ T.β < 1 ∧ 0 ≤ T.γ ∧ T.γ < 1 ∧ T.β + T.γ < 1 ∧ 1 < T.A * T.η

/-- Expected project payoff `u(R) = A R^β`, (2). -/
noncomputable def u (T : Tech) (R : ℝ) : ℝ := T.A * R ^ T.β

/-- Discovery intensity `λ(R) = η R^γ`, (2). -/
noncomputable def lam (T : Tech) (R : ℝ) : ℝ := T.η * R ^ T.γ

/-- Upper end of the investment range, (7): `R̄ = (A η)^{1/(1-(β+γ))}`. -/
noncomputable def Rbar (T : Tech) : ℝ := (T.A * T.η) ^ (1 / (1 - (T.β + T.γ)))

end Tech

/-- The R&D part of the unconstrained monopoly's objective (4) at intensity `R` and discount
rate `r`: the discovery time `τ_d` is exponential with rate `λ(R)`; the firm pays `R` per unit
time on `[0, τ_d]` and receives the expected payoff `u(R)` at `τ_d`, everything discounted at
rate `r`. -/
noncomputable def ucPayoff (T : Tech) (r R : ℝ) : ℝ :=
  ∫ τ, (Real.exp (-r * τ) * T.u R - R * ∫ t in (0 : ℝ)..τ, Real.exp (-r * t))
    ∂(ProbabilityTheory.expMeasure (T.lam R))

/-- `R*_uc`: the set of maximizers of `ucPayoff T r` over the range `[R̲, R̄] = [1, R̄]` of (7). -/
noncomputable def RstarUC (T : Tech) (r : ℝ) : Set ℝ :=
  {R | R ∈ Set.Icc 1 T.Rbar ∧ ∀ R' ∈ Set.Icc 1 T.Rbar, ucPayoff T r R' ≤ ucPayoff T r R}

/-- The paper's `ln V(R) = ln(uλ - R) - ln(λ + r)` of (A.1), the logarithm of the closed form
(5) of the project value. -/
noncomputable def logV (T : Tech) (r R : ℝ) : ℝ :=
  Real.log (T.u R * T.lam R - R) - Real.log (T.lam R + r)

/-- `OrderedAbove S S'`: every element `x` of `S` lies weakly below every element `y` of `S'`,
and strictly below it whenever `x > R̲ = 1`. This is how "`∂R*/∂s > 0`" is posed for optimal
sets. -/
def OrderedAbove (S S' : Set ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S', x ≤ y ∧ (1 < x → x < y)

end AccelScal.UCMonopoly


