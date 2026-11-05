-- Prove2me | Definitions.Def_ReviewInfoShare_Model
-- name    : ReviewInfoShare_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:38:06.483474+00:00
-- url     : https://prove2.me/theorems/29945fee-405c-469e-aae0-12e7c539c134
-- title:
--   Model of reviews and information sharing — data, regimes, $\pi$, $\pi_u$, $\bar u$, signal structure (4)
-- statement:
--   The primitives of the model of Shin and Zeevi.
--
--   1. **Data.** Nominal demand $\alpha$; the mean $\mu_\theta$ and standard deviation $\sigma_\theta$ of the quality sensitivity $\theta$; the standard deviation $\sigma_m$ of the propensity signal around $\theta$; the standard deviation $\sigma_p$ of the unobservable quality component; quality levels $\underline q<\bar q$ with unit costs $\underline c<\bar c$. The common assumptions are $0<\underline q<\bar q$, $\underline c<\bar c$ and $\sigma_\theta,\sigma_m,\sigma_p,\mu_\theta>0$.
--   2. **Decisions and regimes.** The quality $q\in\{\underline q,\bar q\}$ with its cost $c_q$; the arrangement $i\in\{s,ns\}$; the two boundary regimes, no reviews ($\gamma=0$) and perfectly informative reviews ($\gamma=\infty$).
--   3. **Functions of the data.** The signal strength $\phi=\sigma_\theta^2/(\sigma_m^2+\sigma_\theta^2)$ of (4), and
--   $$
--   \pi(q)=(\alpha+\mu_\theta q-c_q)^2,\qquad \pi_u(q)=\Bigl(\alpha+\mu_\theta q-\frac{c_q}{1-u}\Bigr)^2,\qquad \tilde\pi_u(q)=(\alpha+\mu_\theta q)^2-\frac{c_q^2}{(1-u)^2},
--   $$
--   $$
--   \bar u=1-\sqrt{\frac{\bar c^2-\underline c^2}{(\alpha+\mu_\theta\bar q)^2-(\alpha+\mu_\theta\underline q)^2}} .
--   $$
--   The standing commission assumptions are $\pi_u(\bar q)<\pi_u(\underline q)$ and $u\in(0,\bar u)$.
--   4. **Signals.** On a probability space, $\theta$, $s_\theta$ and $\epsilon$ are square-integrable; $E\theta=\mu_\theta$, $\operatorname{Var}\theta=\sigma_\theta^2$; $E[s_\theta\mid\theta]=\theta$ and $E(s_\theta-\theta)^2=\sigma_m^2$; the posterior mean is linear,
--   $$
--   E[\theta\mid s_\theta]=\hat\theta:=(1-\phi)\mu_\theta+\phi s_\theta ;
--   $$
--   and $E\epsilon=0$, $E\epsilon^2=\sigma_p^2$, with $\epsilon$ independent of $(\theta,s_\theta)$.
--   5. **Posterior quality.** $\hat q_2=q$ at $\gamma=0$ and $\hat q_2=q+\epsilon$ at $\gamma=\infty$. The manufacturer's estimate of $\theta$ is $\tilde\theta=\hat\theta$ with sharing and $\tilde\theta=\mu_\theta$ without.
--
--   Every game and every profit of the mission is built on these objects.
--
--   **Formalization Note** The independence of $\epsilon$ from $(\theta,s_\theta)$ is not printed, and (37)–(39) need it. The normal law of $\epsilon$ and the supports of $\theta,s_\theta$ are not assumed; the printed $\theta>0$ survives only as $\mu_\theta>0$. $\operatorname{Var}\hat\theta=\phi\sigma_\theta^2$ is a consequence of these hypotheses, not one of them. `CommissionAssumptions` adds $(\alpha+\mu_\theta\underline q)^2<(\alpha+\mu_\theta\bar q)^2$ and $\underline c^2\le\bar c^2$, so that the radicand of (17) is a nonnegative number over a positive denominator; both follow from $0<\alpha$ and $0\le\underline c$. All objects are bundled in one module because every statement uses them together.
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, §2, pp.9–11, (2), (4); (9), p.16; (17), p.22; (60), p.43

import Mathlib

open MeasureTheory

namespace ReviewInfoShare

/-- The numerical data of Shin–Zeevi, *Product Quality and Information Sharing in the Presence of
Reviews*, SSRN 3886954, §2, pp.9–11: nominal demand `α`, prior mean `μ` (= `µ_θ`) and standard
deviation `σθ` of the quality sensitivity `θ`, standard deviation `σm` of the propensity signal
around `θ`, standard deviation `σp` of the unobservable quality component, the two quality levels
`qL`, `qH` (`q̲`, `q̄`) and their unit costs `cL`, `cH` (`c̲`, `c̄`). -/
structure Params where
  α : ℝ
  μ : ℝ
  σθ : ℝ
  σm : ℝ
  σp : ℝ
  qL : ℝ
  qH : ℝ
  cL : ℝ
  cH : ℝ

/-- The assumptions on the data common to the whole model, SSRN 3886954: `0 < q̲ < q̄` (p.16),
`c̄ > c̲` (p.9), `σ_θ, σ_m > 0` so that `φ ∈ (0,1)` (p.11), `σ_p > 0` (p.9).

**Formalization Note.** The paper has `θ > 0` on a support `[θ̲, θ̄]` (p.9); only the consequence
`µ_θ > 0` is kept. -/
structure Params.Admissible (P : Params) : Prop where
  qL_pos : 0 < P.qL
  qL_lt_qH : P.qL < P.qH
  cL_lt_cH : P.cL < P.cH
  σθ_pos : 0 < P.σθ
  σm_pos : 0 < P.σm
  σp_pos : 0 < P.σp
  μ_pos : 0 < P.μ

/-- The manufacturer's quality decision `q ∈ {q̲, q̄}`, SSRN 3886954, p.9. -/
inductive Quality
  | low
  | high
  deriving DecidableEq

/-- The two boundary regimes of learning compared by Proposition 7, SSRN 3886954, pp.27–28:
no reviews (`γ = 0`) and perfectly informative reviews (`γ = ∞`).

**Formalization Note.** The boundary models are taken directly: `q̂₂ = q` at `γ = 0` by (2), and
`q̂₂ = Q = q + ε` at `γ = ∞`, where `σ_r² = σ_p²/γ = 0`. -/
inductive Regime
  | noReviews
  | perfectReviews
  deriving DecidableEq

/-- The information arrangement `i ∈ {s, ns}`, SSRN 3886954, p.11. -/
inductive Info
  | s
  | ns
  deriving DecidableEq

namespace Params

/-- The quality value of a decision: `q̲` or `q̄`. -/
def qual (P : Params) : Quality → ℝ
  | .low => P.qL
  | .high => P.qH

/-- The unit cost `c_q` of a decision, SSRN 3886954, p.9. -/
def cost (P : Params) : Quality → ℝ
  | .low => P.cL
  | .high => P.cH

/-- The signal strength `φ = σ_θ²/(σ_m² + σ_θ²)`, SSRN 3886954, (4), p.11. -/
noncomputable def phi (P : Params) : ℝ := P.σθ ^ 2 / (P.σm ^ 2 + P.σθ ^ 2)

/-- `π(q) = (α + µ_θ q − c_q)²`, SSRN 3886954, (9), p.16. -/
def pi (P : Params) (q : Quality) : ℝ := (P.α + P.μ * P.qual q - P.cost q) ^ 2

/-- `π_u(q) = (α + µ_θ q − c_q/(1 − u))²`, SSRN 3886954, (17), p.22. -/
noncomputable def piU (P : Params) (u : ℝ) (q : Quality) : ℝ :=
  (P.α + P.μ * P.qual q - P.cost q / (1 - u)) ^ 2

/-- `π̃_u(q) = (α + µ_θ q)² − c_q²/(1 − u)²`, SSRN 3886954, (60), p.43. -/
noncomputable def piTilde (P : Params) (u : ℝ) (q : Quality) : ℝ :=
  (P.α + P.μ * P.qual q) ^ 2 - P.cost q ^ 2 / (1 - u) ^ 2

/-- The bound on the commission rate, `ū = 1 − √((c̄² − c̲²)/((α + µ_θ q̄)² − (α + µ_θ q̲)²))`,
SSRN 3886954, (17), p.22. -/
noncomputable def uBar (P : Params) : ℝ :=
  1 - Real.sqrt ((P.cH ^ 2 - P.cL ^ 2) / ((P.α + P.μ * P.qH) ^ 2 - (P.α + P.μ * P.qL) ^ 2))

end Params

/-- The standing assumptions of the commission contract, SSRN 3886954, p.22: `π_u(q̄) < π_u(q̲)` and
`u ∈ (0, ū)`.

**Formalization Note.** `(α + µ_θ q̲)² < (α + µ_θ q̄)²` and `c̲² ≤ c̄²` say that the radicand of `ū` in (17)
is a nonnegative number over a positive denominator. Both follow from `0 < α` and `0 ≤ c̲`; the only cases
they exclude where (17) is still defined have `c̲ < 0`, which is not a unit cost. -/
structure CommissionAssumptions (P : Params) (u : ℝ) : Prop where
  uBar_den_pos : (P.α + P.μ * P.qL) ^ 2 < (P.α + P.μ * P.qH) ^ 2
  uBar_num_nonneg : P.cL ^ 2 ≤ P.cH ^ 2
  piU_lt : P.piU u .high < P.piU u .low
  u_pos : 0 < u
  u_lt_uBar : u < P.uBar

/-- The random primitives on a sample space: the law `prob`, the quality sensitivity `θ`, the
propensity signal `sθ` and the unobservable quality component `ε` (the paper's `ϵ_q`, with
`Q = q + ϵ_q`), SSRN 3886954, p.9 and p.11. -/
structure Signals (Ω : Type*) [MeasurableSpace Ω] where
  prob : Measure Ω
  θ : Ω → ℝ
  sθ : Ω → ℝ
  ε : Ω → ℝ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The posterior mean `θ̂ = (1 − φ)µ_θ + φ s_θ`, SSRN 3886954, (4), p.11. -/
noncomputable def thetaHat (P : Params) (S : Signals Ω) (ω : Ω) : ℝ :=
  (1 - P.phi) * P.μ + P.phi * S.sθ ω

/-- The manufacturer's estimate of `θ` in the second stage: `θ̃ = θ̂` if it subscribes and
`θ̃ = µ_θ` otherwise, SSRN 3886954, §4.1, p.22. -/
noncomputable def estimate (P : Params) (S : Signals Ω) : Info → Ω → ℝ
  | .s, ω => thetaHat P S ω
  | .ns, _ => P.μ

/-- The second-stage posterior mean quality `q̂₂` in a boundary regime: `q` at `γ = 0` and
`q + ε` at `γ = ∞`, SSRN 3886954, (2), p.10. -/
def qHat2 (P : Params) (S : Signals Ω) : Regime → Quality → Ω → ℝ
  | .noReviews, q, _ => P.qual q
  | .perfectReviews, q, ω => P.qual q + S.ε ω

/-- The information structure of SSRN 3886954, pp.9–11: on a probability space, `θ`, `s_θ`, `ε` are
square-integrable; `θ` has mean `µ_θ` and variance `σ_θ²` (p.9); `s_θ` is an unbiased estimator of
`θ` with variance `σ_m²` (p.11); the posterior mean is the linear expectation (4); and `ε` has mean
`0` and variance `σ_p²` and is independent of `(θ, s_θ)`.

**Formalization Note.** Independence of `ε` from `(θ, s_θ)` is not printed; (37)–(39) need it. The
normal law of `ε` (p.9) is not assumed: two moments suffice, which covers it. The supports
`[θ̲, θ̄]` of `θ` and `s_θ` are not assumed. Conditional expectations are Mathlib's for the
σ-algebras generated by `θ` and `s_θ`, as almost-everywhere identities. -/
structure IsSignalModel (P : Params) (S : Signals Ω) : Prop where
  isProb : IsProbabilityMeasure S.prob
  meas_θ : Measurable S.θ
  meas_sθ : Measurable S.sθ
  meas_ε : Measurable S.ε
  memLp_θ : MemLp S.θ 2 S.prob
  memLp_sθ : MemLp S.sθ 2 S.prob
  memLp_ε : MemLp S.ε 2 S.prob
  mean_θ : ∫ ω, S.θ ω ∂S.prob = P.μ
  var_θ : ∫ ω, (S.θ ω - P.μ) ^ 2 ∂S.prob = P.σθ ^ 2
  unbiased : condExp (MeasurableSpace.comap S.θ inferInstance) S.prob S.sθ =ᵐ[S.prob] S.θ
  var_noise : ∫ ω, (S.sθ ω - S.θ ω) ^ 2 ∂S.prob = P.σm ^ 2
  linear : condExp (MeasurableSpace.comap S.sθ inferInstance) S.prob S.θ
    =ᵐ[S.prob] thetaHat P S
  mean_ε : ∫ ω, S.ε ω ∂S.prob = 0
  var_ε : ∫ ω, S.ε ω ^ 2 ∂S.prob = P.σp ^ 2
  indep : ProbabilityTheory.IndepFun S.ε (fun ω => (S.θ ω, S.sθ ω)) S.prob

end ReviewInfoShare


