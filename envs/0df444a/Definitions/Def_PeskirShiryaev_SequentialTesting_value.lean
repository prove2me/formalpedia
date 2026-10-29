-- Prove2me | Definitions.Def_PeskirShiryaev_SequentialTesting_value
-- name    : PeskirShiryaev_SequentialTesting_value
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:09.290669+00:00
-- url     : https://prove2.me/theorems/1987ff31-2d49-49cd-a7e9-9c863fd22067
-- title:
--   Admissible tests, Bayesian risk, variational value and exit times
-- statement:
--   For the Wiener experiment, let $\tau$ be a nonnegative elapsed stopping time of the observation filtration, bounded by a remaining horizon $h$. A binary terminal decision $d$ is measurable at $\tau$: each event $\{d=1,\tau\le u\}$ belongs to $\mathcal F^X_u$. Define the Bayesian risk and posterior stopping value by
--   $$R_p(\tau,d)=E_p[\tau+a\mathbf1_{\{d=0,\theta=1\}}+b\mathbf1_{\{d=1,\theta=0\}}],\qquad V(t,p)=\inf_{0\le\tau\le T-t}E_p[t+\tau+H(\Pi^p_\tau)].$$
--   The process is restarted with prior $p$ at elapsed time zero; $t$ is the absolute clock. The lower and upper boundaries are the supremum and infimum of the contact sets $V(t,p)=t+H(p)$ on $[0,c]$ and $[c,1]$, with both assigned $c$ at $T$. Thus the boundaries are constructed from the value.
--
--   For proposed boundaries $g_0,g_1$, the exit time is the first elapsed $u\le T-t$ with $\Pi^p_u\notin(g_0(t+u),g_1(t+u))$, using $T-t$ when the set is empty. The cutoff decision accepts hypothesis one if $\Pi^p_\tau\ge c$. Separately, the printed decision relation allows only $(\Pi^p_\tau=g_1(\tau),d=1)$ or $(\Pi^p_\tau=g_0(\tau),d=0)$, exactly exposing its missing branches.
--
--   These objects distinguish the original testing loss from its posterior reduction and the optimal boundaries from arbitrary candidates.
--
--   **Formalization Note** Admissible stopping times have measurable representatives with pointwise bounds. Finite-horizon costs are real Bochner integrals; on the stated domains they are integrable and the infimum is nonempty and bounded. No information about the latent hypothesis or driving noise is added to the observation filtration. Values outside the stated time and prior domains are not used in the theorem claims.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 288, 292–293, 298–300 / PDF pp. 305, 309–310, 315–317, Eqs. (21.0.4)–(21.0.5), (21.2.1), (21.2.6)–(21.2.7), (21.2.33), (21.2.44)–(21.2.45)

import Definitions.Def_PeskirShiryaev_SequentialTesting_Model

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PeskirShiryaev.SequentialTesting

/-- A nonnegative elapsed stopping time for the raw observation filtration,
with a pointwise finite bound. The explicit ambient measurability condition
is redundant for bounded stopping times, and makes representatives explicit. -/
def Admissible {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (h : ℝ) (τ : Ω → ℝ≥0) : Prop :=
  Measurable τ ∧ (∀ ω, (τ ω : ℝ) ≤ h) ∧
    ∀ u : ℝ≥0, MeasurableSet[observationSigma E C u] {ω | τ ω ≤ u}

/-- Stopped-sigma-field measurability of a binary decision, expressed by its
true-event intersections with {τ ≤ u}. -/
def AdmissibleDecision {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (τ : Ω → ℝ≥0) (d : Ω → Bool) : Prop :=
  Measurable d ∧ ∀ u : ℝ≥0,
    MeasurableSet[observationSigma E C u] {ω | d ω = true ∧ τ ω ≤ u}

noncomputable def stoppingCost {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (t p : ℝ) (τ : Ω → ℝ≥0) : ℝ :=
  ∫ ω, t + (τ ω : ℝ) + terminalLoss C (posterior E C p (τ ω) ω) ∂prior E p

/-- The value of (21.2.1), including the absolute clock t, defined by all
admissible stopping times independently of any boundary or candidate solution. -/
noncomputable def value {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (t p : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ τ : Ω → ℝ≥0,
    Admissible E C (C.T - t) τ ∧ v = stoppingCost E C t p τ}

/-- The actual two-error Bayesian cost, as opposed to the posterior cost. -/
noncomputable def bayesRisk {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (p : ℝ) (τ : Ω → ℝ≥0) (d : Ω → Bool) : ℝ :=
  ∫ ω, (τ ω : ℝ) +
    (if d ω = false ∧ E.θ ω = true then C.a else 0) +
    (if d ω = true ∧ E.θ ω = false then C.b else 0) ∂prior E p

noncomputable def thresholdDecision {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (p : ℝ) (τ : Ω → ℝ≥0) (ω : Ω) : Bool :=
  if cutoff C ≤ posterior E C p (τ ω) ω then true else false

/-- Boundary 0 is the supremum of the lower contact set; boundary 1 is the
infimum of the upper contact set. Both equal the cutoff at the terminal time.
The contact sets are computed from the variational value, not postulated. -/
noncomputable def optimalBoundary {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (i : Fin 2) (t : ℝ) : ℝ :=
  if t = C.T then cutoff C else
    if i = 0 then
      sSup {p : ℝ | p ∈ Icc 0 (cutoff C) ∧ value E C t p = t + terminalLoss C p}
    else
      sInf {p : ℝ | p ∈ Icc (cutoff C) 1 ∧ value E C t p = t + terminalLoss C p}

/-- First exit in elapsed time; the empty-set convention is the remaining
horizon, as in (21.2.33). -/
noncomputable def exitTime {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (g : Fin 2 → ℝ → ℝ) (t p : ℝ) (ω : Ω) : ℝ≥0 := by
  classical
  let S := {u : ℝ≥0 | (u : ℝ) ≤ C.T - t ∧
    posterior E C p u ω ∉ Ioo (g 0 (t + u)) (g 1 (t + u))}
  exact if S.Nonempty then sInf S else (C.T - t).toNNReal

/-- Graph of the two cases actually printed in (21.2.45), with no invented
otherwise branch. Existence of a decision taking values in this graph is part
of the faithful theorem, including its missing immediate-stop cases (F1). -/
def PrintedDecision {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (g : Fin 2 → ℝ → ℝ) (p : ℝ)
    (τ : Ω → ℝ≥0) (d : Ω → Bool) : Prop :=
  ∀ᵐ ω ∂prior E p,
    (posterior E C p (τ ω) ω = g 1 (τ ω) ∧ d ω = true) ∨
    (posterior E C p (τ ω) ω = g 0 (τ ω) ∧ d ω = false)

end PeskirShiryaev.SequentialTesting


