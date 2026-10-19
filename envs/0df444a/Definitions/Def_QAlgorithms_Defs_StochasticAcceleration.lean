-- Prove2me | Definitions.Def_QAlgorithms_Defs_StochasticAcceleration
-- name    : QAlgorithms_Defs_StochasticAcceleration
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:25:35.895218+00:00
-- url     : https://prove2.me/theorems/cad44811-f3f9-4245-97c4-8b2a2a93e096
-- title:
--   StochasticAcceleration
-- statement:
--   StochasticAcceleration
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\StochasticAcceleration.lean

import Definitions.Def_QAlgorithms_Defs_StochasticMeanPrograms
import Definitions.Def_QAlgorithms_Defs_GaussianSmoothing
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.StochasticOptimization

variable {n m d k b w M K N c out : ℕ}

/-- Public positive parameters for Algorithm 3, 2308.01582 p.13. -/
structure AccelerationParameters where
  dimension : ℕ
  dimension_pos : 0 < dimension
  L : ℝ
  R : ℝ
  eps : ℝ
  L_pos : 0 < L
  R_pos : 0 < R
  eps_pos : 0 < eps
  T : ℕ
  sigma : ℝ
  radius : ℝ
  gamma : ℝ

/-- Printed constants and the disclosed ceiling for the real update
budget, 2308.01582 p.13 Algorithm 3. -/
def acceleratedParameters (d : ℕ) (hd : 0 < d) (L R eps : ℝ)
    (hL : 0 < L) (hR : 0 < R) (heps : 0 < eps) : AccelerationParameters :=
  let T := ⌈4 * (d : ℝ) ^ (1 / 4 : ℝ) * L * R / eps⌉₊
  let sigma := (d : ℝ) ^ (1 / 8 : ℝ) / 8 * Real.sqrt (L * eps / R)
  let r := eps / (4 * Real.sqrt d * L)
  ⟨d,hd,L,R,eps,hL,hR,heps,T,sigma,r,
    R * Real.sqrt (6 * (L/r)) / (((T : ℝ) + 2) ^ (3 / 2 : ℝ) * sigma)⟩

/-- Radial Euclidean ball projection for the printed xmd-centered
quadratic proximal step (2308.01582 p.13 line 7). -/
def ballProx {d : ℕ} (R r L gamma : ℝ) (hR : 0 ≤ R) (hr : 0 < r) (hL : 0 < L)
    (xmd g : Vector d) : Vector d :=
  let v := xmd - (r * gamma / L) • g
  if ‖v‖ ≤ R then v else (R / ‖v‖) • v

/-- Algorithm-3 iteration constructor on an actual operational gradient
subroutine (2308.01582 p.13). The subroutine is fixed before the objective;
neither gradients nor their distribution are received for free. -/
def acceleratedLoop {d : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (sampleGradient : Vector d → ContinuousOracleProgram d H)
    (R r L gamma : ℝ) (hR : 0 ≤ R) (hr : 0 < r) (hL : 0 < L) :
    ℕ → ℕ → Vector d → Vector d → ContinuousOracleProgram d H
  | 0, _, _, xag => .output xag
  | fuel + 1, t, x, xag =>
      let beta := ((t : ℝ) + 1) / 2
      let xmd := beta⁻¹ • x + (1-beta⁻¹) • xag
      .bind (sampleGradient xmd) fun g =>
        let xn := ballProx R r L (((t : ℝ) + 1) * gamma / 2) hR hr hL xmd g
        acceleratedLoop sampleGradient R r L gamma hR hr hL fuel (t+1) xn
          (beta⁻¹ • xn + (1-beta⁻¹) • xag)

/-- Expand every forward/inverse sampling query into the counted Gaussian
preparation/original-query/swap word (2308.01582 pp.13–14).
All mean-estimator and variance-reduction code remains actual program data. -/
def expandSmoothedQueries {d : ℕ} {H W : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    {registers : GradientRegisters d H W} {r : ℝ} {hr : 0 < r}
    (layout : GaussianQueryLayout d H W registers r hr) (x : Vector d) :
    ContinuousOracleProgram d H → ContinuousOracleProgram d H
  | .output v => .output v
  | .known U next => .known U (expandSmoothedQueries layout x next)
  | .query inverse next => smoothedQueryWord layout x inverse (expandSmoothedQueries layout x next)
  | .measure next => .measure fun v => expandSmoothedQueries layout x (next v)
  | .naturalDraw mu hmu next => .naturalDraw mu hmu fun j => expandSmoothedQueries layout x (next j)
  | .bind first next => .bind (expandSmoothedQueries layout x first)
      (fun v => expandSmoothedQueries layout x (next v))
  | .fresh next => .fresh (expandSmoothedQueries layout x next)
  | .diverge => .diverge

/-- Public Algorithm-3 schedule and actual Algorithm-2 gradient calls,
2308.01582 p.13. Mean-estimator and Gaussian layouts are public code chosen
before f and its oracle. Every smoothed query expands to one original
forward/inverse query. Degenerate/already-accurate cases return zero. -/
def acceleratedProgram {d : ℕ} {H W : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    {registers : GradientRegisters d H W}
    (M : QuantumMeanEstimationProgram d H)
    (layouts : (r : ℝ) → (hr : 0 < r) → GaussianQueryLayout d H W registers r hr)
    (L R eps : ℝ) : ContinuousOracleProgram d H :=
  if hd : 0 < d then
    if h : 0 < L ∧ 0 < R ∧ 0 < eps ∧ eps < L*R then
      let P := acceleratedParameters d hd L R eps h.1 h.2.1 h.2.2.1
      if hr : 0 < P.radius then
        let estimateAt := fun x => expandSmoothedQueries (layouts P.radius hr) x
          (quantumVarianceReduction M L P.sigma)
        acceleratedLoop estimateAt R P.radius L P.gamma h.2.1.le hr h.1 P.T 1 0 0
      else .diverge
    else .output 0
  else .output 0

/-- Mass-one integrable expected-gap contract, 2308.01582 pp.2,5,13–15.
It is a theorem conclusion on the operational law, not algorithm data. -/
def ExpectedOptimizationContract {d : ℕ} (law : Measure (Vector d × ℕ))
    (f : Vector d → ℝ) (xstar : Vector d) (eps : ℝ) : Prop :=
  law Set.univ = 1 ∧ Integrable (fun vq => f vq.1 - f xstar) law ∧
    ∫ vq, f vq.1 - f xstar ∂law ≤ eps

/-- Uniform soft expected-query bound, 2308.01582 pp.3,13–15.
Constants precede all dimensions and public parameters; no gate or
worst-case call guarantee is asserted. -/
def SoftExpectedQueryBound {Input : ℕ → ℝ → ℝ → ℝ → Type*}
    (cost : (d : ℕ) → (L R eps : ℝ) → Input d L R eps → ℝ≥0∞) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∃ threshold : ℝ, 1 ≤ threshold ∧
    ∀ d L R eps, 1 ≤ d → 0 < L → 0 < R → 0 < eps → threshold ≤ L*R/eps →
      ∀ input : Input d L R eps,
      cost d L R eps input ≤ ENNReal.ofReal (C * (d : ℝ) ^ (5/8 : ℝ) *
        (L*R/eps) ^ (3/2 : ℝ) *
        max 1 (Real.log (2+d) + |Real.log eps| + |Real.log L| + |Real.log R|)^p)

/-- Sanity check for the modeled source objects (arxiv-2308.01582v2, PDF pp.2,3,5,13,15). -/
example {d : ℕ} (R r L gamma : ℝ) (hR : 0 ≤ R) (hr : 0 < r) (hL : 0 < L) :
    ballProx R r L gamma hR hr hL (0 : Vector d) 0 = 0 := by
  simp [ballProx, hR]

/-- Sanity check for the modeled source objects (arxiv-2308.01582v2, PDF pp.2,3,5,13,15). -/
example {d : ℕ} {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    {registers : GradientRegisters d H W} (M : QuantumMeanEstimationProgram d H)
    (layouts : (r : ℝ) → (hr : 0 < r) → GaussianQueryLayout d H W registers r hr)
    (R eps : ℝ) :
    acceleratedProgram M layouts 0 R eps = .output 0 := by
  simp [acceleratedProgram]

end QAlgorithms.StochasticOptimization


