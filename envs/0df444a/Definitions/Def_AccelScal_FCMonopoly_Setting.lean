-- Prove2me | Definitions.Def_AccelScal_FCMonopoly_Setting
-- name    : AccelScal_FCMonopoly_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:40.910341+00:00
-- url     : https://prove2.me/theorems/d3c114c4-991d-4c4b-a01a-7dedc8a45430
-- title:
--   §2, (2), Lemma 1 (5)–(6), (7), pp. 3–5 — power-form R&D technology, the reduced UC and FC project values, and their sets of optimal intensities
-- statement:
--   This file fixes the objects of Lin's comparison between a financially constrained (FC) and a financially unconstrained (UC) monopoly R&D investor.
--
--   **Technology.** A project is described by four parameters $(A,\beta,\eta,\gamma)$. At investment intensity $R$ (R&D spending per unit of time) the expected discovery payoff and the discovery rate are
--   $$u(R)=A\,R^{\beta},\qquad \lambda(R)=\eta\,R^{\gamma}.$$
--   The **standing assumptions** are those of (2), $A>0$, $\eta>0$, $\beta,\gamma\in[0,1)$, $\beta+\gamma<1$, together with $A\eta>1$, which says that investment takes place: the project value at the lowest intensity $\underline R=1$ is positive. The upper end of the investment range (7) is
--   $$\bar R=(A\eta)^{1/(1-(\beta+\gamma))}.$$
--
--   **Values.** For a discount rate $r$, the UC project value at intensity $R$ is the perpetuity of Lemma 1, (5),
--   $$V_{uc}(R)=\frac{u(R)\lambda(R)-R}{\lambda(R)+r}.$$
--   For an FC firm whose AIP cash flow follows a geometric Brownian motion with drift $\mu$ and volatility $\sigma$ and starts at $X$, the project value at intensity $R$ is that of Lemma 1, (6),
--   $$V_{fc}(R)=\frac{u(R)\lambda(R)-R}{\lambda(R)+r}\left(1-\Big(\frac{X}{R}\Big)^{\alpha}\right),\qquad \alpha=\frac12-\frac{\mu}{\sigma^2}-\sqrt{\Big(\frac12-\frac{\mu}{\sigma^2}\Big)^2+\frac{2(\lambda(R)+r)}{\sigma^2}}.$$
--
--   **Optimal intensities.** $R^*_{uc}$ is the set of maximizers of $V_{uc}$ over the range $[\underline R,\bar R]=[1,\bar R]$ of (7), and $R^*_{fc}$ is the set of maximizers of $V_{fc}$ over the range $[\underline R,\min\{\bar R,X\}]=[1,\min\{\bar R,X\}]$ of (7).
--
--   These objects are shared by every statement of the mission: the goal (Corollary 1) and its two first-order-condition milestones.
--
--   **Formalization Note.** The FC firm's original problem (3) is an expectation over a geometric Brownian cash flow and its first-passage time below $R$; that its value equals (6) is the paper's Lemma 1 (Appendix A.12), which needs first-passage substrate not available in Mathlib and is not posed. The mission therefore takes the reduced values (5) and (6) as the definitions of the two firms' problems, exactly as the proof of Corollary 1 (Appendix A.4) does. The random payoff $\tilde u$ is replaced by its mean $u(R)$, and the AIP term of (3)/(4), which does not depend on $R$, is dropped. Powers are `Real.rpow`. Optimal intensities are sets of maximizers, never a selected or closed-form value. The hypothesis $A\eta>1$ is added to (2) (the paper's "conditional on investment taking place", p. 5).
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, pp. 3–5, (2), Lemma 1 (5)–(6), (7)

import Mathlib

namespace AccelScal.FCMonopoly

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

/-- Lemma 1's exponent `α = 1/2 - μ/σ² - √((1/2 - μ/σ²)² + 2(λ(R) + r)/σ²)`. -/
noncomputable def alpha (T : Tech) (r μ σ R : ℝ) : ℝ :=
  1 / 2 - μ / σ ^ 2 - Real.sqrt ((1 / 2 - μ / σ ^ 2) ^ 2 + 2 * (T.lam R + r) / σ ^ 2)

/-- The unconstrained monopoly's R&D project value at intensity `R`, (5):
`(u(R) λ(R) - R) / (λ(R) + r)`. -/
noncomputable def ucValue (T : Tech) (r R : ℝ) : ℝ :=
  (T.u R * T.lam R - R) / (T.lam R + r)

/-- The financially constrained monopoly's R&D project value at intensity `R`, (6):
`(u(R) λ(R) - R) / (λ(R) + r) · (1 - (X/R)^α)`. -/
noncomputable def fcValue (T : Tech) (r μ σ X R : ℝ) : ℝ :=
  ucValue T r R * (1 - (X / R) ^ alpha T r μ σ R)

/-- The set of maximizers of `V` over a set `S`. -/
def maximizers (V : ℝ → ℝ) (S : Set ℝ) : Set ℝ :=
  {R | R ∈ S ∧ ∀ R' ∈ S, V R' ≤ V R}

/-- `R*_uc`: the set of optimal intensities of (5) over the range `[R̲, R̄] = [1, R̄]` of (7). -/
noncomputable def RstarUC (T : Tech) (r : ℝ) : Set ℝ :=
  maximizers (ucValue T r) (Set.Icc 1 T.Rbar)

/-- `R*_fc`: the set of optimal intensities of (6) over the range `[R̲, min{R̄, X}]` of (7). -/
noncomputable def RstarFC (T : Tech) (r μ σ X : ℝ) : Set ℝ :=
  maximizers (fcValue T r μ σ X) (Set.Icc 1 (min T.Rbar X))

end AccelScal.FCMonopoly


