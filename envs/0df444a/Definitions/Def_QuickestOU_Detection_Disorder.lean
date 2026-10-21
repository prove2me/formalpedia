-- Prove2me | Definitions.Def_QuickestOU_Detection_Disorder
-- name    : QuickestOU_Detection_Disorder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:27.561987+00:00
-- url     : https://prove2.me/theorems/bd9f2e2c-bad8-47d9-a774-4139aafee865
-- title:
--   §3 — Bayesian OU disorder model and initial Bayes risk
-- statement:
--   Under the disorder law, an unobserved time $\theta$ is independent of the Brownian driver and has distribution $\pi\delta_0+(1-\pi)\operatorname{Exp}(\lambda)$. The observed process $X$ starts at $x$, has unit diffusion coefficient and mean-reversion rate $\beta_0$ before $\theta$ and $\beta_1$ from $\theta$ onward. Stopping decisions use only the natural filtration of $X$. Their risk and optimal value are
--
--   $$R(\tau)=\mathsf P_\pi(\tau<\theta)+c\,\mathsf E_\pi(\tau-\theta)^+,\qquad V(\pi)=\inf_{\tau\in\mathcal T^X}R(\tau).$$
--
--   The model also names the conditional posterior probability $\Pi_t=\mathsf P_\pi(\theta\le t\mid\mathcal F_t^X)$ and the first crossing rule built from the explicit odds functional.
--
--   This is the original Bayesian objective later recovered from the no-change stopping problem.
--
--   **Formalization Note** Stopping times take values in $[0,\infty]$; an infinite stopping time has infinite delay. Both Brownian and observed paths are continuous and pointwise measurable versions. The mean levels are zero and diffusion coefficient is one.
-- source:
--   Glover & Peskir, Quickest detection problems for Ornstein–Uhlenbeck processes, Research Report No. 11 (2017, revised), Probab. Statist. Group Manchester; to appear in Math. Oper. Res.; https://doi.org/10.1287/moor.2021.0186; pp. 5–8, (3.1)–(3.5), (3.11)

import Mathlib
import Definitions.Def_QuickestOU_Detection_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuickestOU.Detection

/-- The observed OU disorder model of (3.1)--(3.3), with levels zero and noise one. -/
structure DisorderModel (P : Params) (p0 x : ℝ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  μ : Measure Ω
  B : ℝ≥0 → Ω → ℝ
  driver : Driver μ B
  θ : Ω → ℝ
  θ_meas : Measurable θ
  θ_law : μ.map θ = ENNReal.ofReal p0 • Measure.dirac (0 : ℝ) +
    ENNReal.ofReal (1 - p0) • expMeasure P.lam
  indep : Indep (MeasurableSpace.comap θ inferInstance)
    (⨆ t, MeasurableSpace.comap (B t) inferInstance) μ
  X : ℝ≥0 → Ω → ℝ
  X_cont : ∀ ω, Continuous (fun t => X t ω)
  X_meas : ∀ t, Measurable (X t)
  X_eq : ∀ ω t, X t ω = x - P.beta0 *
    (∫ s in (0 : ℝ)..(t : ℝ), X s.toNNReal ω) +
    P.delta * (∫ s in (0 : ℝ)..(t : ℝ),
      if θ ω ≤ s then X s.toNNReal ω else 0) + B t ω

attribute [instance] DisorderModel.mΩ

/-- The observation filtration, excluding the unobserved disorder time. -/
noncomputable def natX {P : Params} {p0 x : ℝ} (M : DisorderModel P p0 x) :
    Filtration ℝ≥0 M.mΩ :=
  Filtration.natural M.X (fun t => (M.X_meas t).stronglyMeasurable)

/-- The false-alarm event τ < θ, with τ = ∞ never a false alarm. -/
def falseAlarm {P : Params} {p0 x : ℝ} (M : DisorderModel P p0 x)
    (τ : M.Ω → WithTop ℝ≥0) : Set M.Ω :=
  {ω | ∃ t : ℝ≥0, τ ω = t ∧ (t : ℝ) < M.θ ω}

/-- Delay after disorder; an infinite stop has infinite delay. -/
noncomputable def detectionDelay {P : Params} {p0 x : ℝ}
    (M : DisorderModel P p0 x) (τ : M.Ω → WithTop ℝ≥0) (ω : M.Ω) : ℝ≥0∞ :=
  if τ ω = ⊤ then ⊤ else ENNReal.ofReal (((τ ω).untopD 0 : ℝ≥0) - M.θ ω)

/-- The initial Bayes risk (3.4), in extended nonnegative reals. -/
noncomputable def risk {P : Params} {p0 x : ℝ}
    (M : DisorderModel P p0 x) (τ : M.Ω → WithTop ℝ≥0) : ℝ≥0∞ :=
  M.μ (falseAlarm M τ) + ENNReal.ofReal P.c * ∫⁻ ω, detectionDelay M τ ω ∂M.μ

/-- The value V(π) in (3.4), over all stopping times of the observed process X. -/
noncomputable def Vpi {P : Params} {p0 x : ℝ} (M : DisorderModel P p0 x) : ℝ≥0∞ :=
  sInf {v | ∃ τ : M.Ω → WithTop ℝ≥0,
    IsStoppingTime (natX M) τ ∧ v = risk M τ}

/-- Posterior probability of θ ≤ t given X's observations through t, (3.5). -/
noncomputable def postProb {P : Params} {p0 x : ℝ}
    (M : DisorderModel P p0 x) (t : ℝ≥0) : M.Ω → ℝ :=
  M.μ[(fun ω => if M.θ ω ≤ (t : ℝ) then (1 : ℝ) else 0) | natX M t]

/-- Corollary 12's stopping time: the first odds crossing of the candidate boundary. -/
noncomputable def tauStar {P : Params} {p0 x : ℝ}
    (M : DisorderModel P p0 x) (a : ℝ → ℝ) : M.Ω → WithTop ℝ≥0 :=
  hittingAfter (fun t ω =>
    (odds P (fun s => M.X s ω) x (p0 / (1 - p0)) t, M.X t ω))
    {q | a q.2 ≤ q.1} 0

end QuickestOU.Detection


