-- Prove2me | Definitions.Def_SKHessianAscent_Localization
-- name    : SKHessianAscent_Localization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-22T19:54:34.564737+00:00
-- url     : https://prove2.me/theorems/df7da220-f295-45a1-b062-dc486bbff702
-- title:
--   Stochastic localization of $\mu_{\beta A}$, $A\sim\mathrm{GOE}(n)$: the tilt $y_t=t\sigma+B_t$, the magnetization $m_t$ and the covariance $Q_t$
-- statement:
--   The paper's ideal process is stochastic localization of the Gibbs measure $\mu=\mu_{\beta A}$ (equations (SL), (HD), (3.1)):
--   $$dy_t=m_t\,dt+dB_t,\quad y_0=0,\qquad m_t=\langle\sigma\rangle_{y_t}=\mathbf E_{\mu_{y_t}}\sigma,\qquad Q_t=\mathrm{Cov}(\mu_{y_t}),$$
--   where $\mu_y(\sigma)\propto\mu(\sigma)e^{\langle y,\sigma\rangle}$.
--
--   An `SLProcess β n P` on a probability space $(\Omega,P)$ consists of:
--
--   1. a measurable disorder matrix $A$ and a measurable sample $\sigma\in\{\pm1\}^n$ whose joint law is: $A\sim\mathrm{GOE}(n)$ and, conditionally on $A$, $\sigma\sim\mu_{\beta A}$;
--   2. a standard Brownian motion $B=(B_t)_{t\ge0}$ in $\mathbb R^n$, independent of $(A,\sigma)$.
--
--   From these, `y t` is the tilt $y_t=t\sigma+B_t$, `mu t` is $\mu_{y_t}=\mu_{\beta A,y_t}$, `mag t` is $m_t=\langle\sigma\rangle_{y_t}$ and `cov t` is $Q_t=\mathrm{Cov}(\mu_{y_t})$.
--
--   This is the process over which desiderata (d1) and (d2a) are stated.
--
--   **Formalization Note** The process is given in the posterior form used on p. 13 of the paper ("The SL process is given by $y_t=t\sigma+B_t$, i.e. $dy_t=\sigma\,dt+dB_t$, where $\sigma\sim\mu_{\beta A}$"); jointly with $A$ it has the same law as the solution of (SL). Wiener measure is not constructed: theorems quantify over every probability space carrying such data. $\mathrm{GOE}(n)$ is the published `RandMatDisc.goe` (symmetric, off-diagonal entries $N(0,1/n)$, diagonal entries $N(0,2/n)$, the normalization of the series, see arXiv:2605.03718, p. 1). Brownian motion is the published `SKAnnealing.Sampling.IsStdBrownian` (independent Mathlib `IsBrownianReal` coordinates, time `ℝ≥0`). The joint law of $(A,\sigma)$ is specified by $P(A\in S,\sigma=s)=\int_S\mu_{\beta a}(s)\,d\mathrm{GOE}(n)(a)$ for measurable $S$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3 p. 7, equations (SL), (HD), (3.1); posterior form on p. 13

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKAnnealing_Sampling_IsStdBrownian
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKHessianAscent

/-!
# Stochastic localization of the SK Gibbs measure

H. Lee, J. S. Sandhu, J. Shi, *Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick
model at β < 1*, §3 (p. 7), equations (SL), (HD), (3.1): `dy_t = m_t dt + dB_t`, `y_0 = 0`,
`m_t = ⟨σ⟩_{y_t}`, `Q_t = Cov(μ_{y_t})`, where `μ_y(σ) ∝ μ(σ) e^{⟨y,σ⟩}` and `μ = μ_{βA}`.

**Formalization Note.** The process is given in its posterior form, which the paper uses on p. 13
("The SL process is given by `y_t = tσ + B_t`, i.e. `dy_t = σ dt + dB_t`, where `σ ∼ μ_{βA}`"):
on a probability space carrying the disorder `A ∼ GOE(n)`, a sample `σ` with conditional law
`μ_{βA}` given `A`, and a standard Brownian motion `B` in `ℝ^n` independent of `(A, σ)`, the tilt
is `y_t = tσ + B_t`. It has the same law, jointly with `A`, as the solution of (SL). Wiener
measure is not constructed: statements quantify over every probability space carrying such a
triple. The GOE law is the published `RandMatDisc.goe` (symmetric, off-diagonal variance `1/n`,
diagonal variance `2/n`), and Brownian motion is the published
`SKAnnealing.Sampling.IsStdBrownian` (independent Mathlib `IsBrownianReal` coordinates, time
`ℝ≥0`).
-/

/-- The data of stochastic localization for `μ_{βA}`, `A ∼ GOE(n)`, on a probability space
`(Ω, P)`: the disorder `A`, the sample `σ`, and the Brownian motion `B`. -/
structure SLProcess (β : ℝ) (n : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The disorder matrix. -/
  A : Ω → Fin n → Fin n → ℝ
  /-- The sample `σ ∼ μ_{βA}`. -/
  σ : Ω → Spin n
  /-- The driving Brownian motion. -/
  B : ℝ≥0 → Ω → (Fin n → ℝ)
  /-- `P` is a probability measure. -/
  prob : IsProbabilityMeasure P
  /-- `A` is measurable. -/
  measurable_A : Measurable A
  /-- `σ` is measurable. -/
  measurable_σ : Measurable σ
  /-- Joint law of `(A, σ)`: `A ∼ GOE(n)` and, given `A`, `σ ∼ μ_{βA}`. -/
  law : ∀ (S : Set (Fin n → Fin n → ℝ)), MeasurableSet S → ∀ s : Spin n,
    P {ω | A ω ∈ S ∧ σ ω = s} =
      ∫⁻ a in S, ENNReal.ofReal (gibbsSK β (Matrix.of a) s) ∂(RandMatDisc.goe n)
  /-- `B` is a standard Brownian motion in `ℝ^n`. -/
  brownian : IsStdBrownian B P
  /-- `B` is independent of `(A, σ)`. -/
  indep : IndepFun (fun ω => (A ω, σ ω)) (fun ω => fun t : ℝ≥0 => B t ω) P

namespace SLProcess

variable {β : ℝ} {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The disorder as a matrix. -/
def mat (X : SLProcess β n P) (ω : Ω) : Matrix (Fin n) (Fin n) ℝ := Matrix.of (X.A ω)

/-- The localization tilt `y_t = tσ + B_t`. -/
noncomputable def y (X : SLProcess β n P) (t : ℝ≥0) (ω : Ω) : Fin n → ℝ :=
  (t : ℝ) • spinVec (X.σ ω) + X.B t ω

/-- The localized measure `μ_{y_t}`. -/
noncomputable def mu (X : SLProcess β n P) (t : ℝ≥0) (ω : Ω) : Spin n → ℝ :=
  tiltSK β (X.mat ω) (X.y t ω)

/-- The magnetization `m_t = ⟨σ⟩_{y_t}`. -/
noncomputable def mag (X : SLProcess β n P) (t : ℝ≥0) (ω : Ω) : Fin n → ℝ :=
  meanVec (X.mu t ω)

/-- The covariance `Q_t = Cov(μ_{y_t})`. -/
noncomputable def cov (X : SLProcess β n P) (t : ℝ≥0) (ω : Ω) : Matrix (Fin n) (Fin n) ℝ :=
  lawCov (X.mu t ω)

end SLProcess

end SKHessianAscent


