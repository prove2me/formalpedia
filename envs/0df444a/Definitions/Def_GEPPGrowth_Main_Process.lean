-- Prove2me | Definitions.Def_GEPPGrowth_Main_Process
-- name    : GEPPGrowth_Main_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:36:59.598906+00:00
-- url     : https://prove2.me/theorems/33ebeb5c-2bc0-45b5-a644-60aedd2595bc
-- title:
--   Gaussian covariance transition law and finite trajectories
-- statement:
--   A covariance matrix is stored in a countable coordinate array, padded with zeros outside its active leading block. After $t$ updates of an $n\times n$ input the active dimension is $n-t$, corresponding to source step $k=t+1$. For a state $S$ of active dimension $D>0$, the transition distribution is
--
--   $$K_D(S,\cdot)=\operatorname{Law}(\mathcal U(S,y)),\qquad y\sim N(0,S).$$
--
--   The initial state is $I_n$. Both the marginal law $\mu_{n,t}$ and the full finite trajectory law are defined by successive integrations against these explicit transitions. At dimension zero the state stays fixed. The covariance along actual GEPP is computed by the same update using the actual observed residual columns, without an assumed growth property.
--
--   The conditional residual law is expressed by a measurable function of the first $t$ original columns together with an integral identity against every measurable history event and every measurable residual event. Its residual distribution is the product of the independent centered Gaussian columns with the actual covariance. This avoids conditioning on a single history of probability zero. Normalization, transition measurability and agreement with actual GEPP are separate theorem obligations.
--
--   The deterministic quantity in Proposition 5.3 is
--
--   $$N_d=\frac{n}{e^{1+1/(d+1)}(d+1+2\log n)}.$$
--
--   All Gaussian draws remain continuous and unbounded; zero padding changes only the storage carrier.
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), §3 and Proposition 3.1, printed pp.6–7, PDF pp.7–8; Proposition 5.3, printed p.18, PDF p.19

import Definitions.Def_GEPPGrowth_Main_GEPP
import Definitions.Def_GEPPGrowth_Main_Conic
import Definitions.Def_GEPPGrowth_Main_ChiSquare
import Definitions.Def_GEPPGrowth_Main_Wishart
import Definitions.Def_GEPPGrowth_Main_ThinQR
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Zero-padded matrices are a single measurable carrier for changing dimensions.
At time t only the leading (n-t)-square block is used. -/
abbrev CovState := ℕ → ℕ → ℝ

def block (S : CovState) (d : ℕ) : Mat d := fun i j => S i.val j.val

def embed {d : ℕ} (S : Mat d) : CovState :=
  fun i j => if hi : i < d then if hj : j < d then S ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

def stateUpdate : (d : ℕ) → CovState → (ℕ → ℝ) → CovState
  | 0, S, _ => S
  | d+1, S, y => embed (update (block S (d+1)) (fun j => y j.val))

/-- Explicit Gaussian transition distribution: sample a fresh residual column and update.
Measurability and normalization are theorem obligations, never model assumptions. -/
noncomputable def covStep : ℕ → CovState → Measure CovState
  | 0, S => Measure.dirac S
  | d+1, S => (normal (block S (d+1))).map (fun y => embed (update (block S (d+1)) y))

/-- Marginal law after t covariance updates, starting with identity. -/
noncomputable def covLaw (n : ℕ) : ℕ → Measure CovState
  | 0 => Measure.dirac (embed (1 : Mat n))
  | t+1 => (covLaw n t).bind (covStep (n-t))

/-- Full finite trajectory law (including time zero), from the same transitions. -/
noncomputable def trajectoryLaw (n : ℕ) : (t : ℕ) → Measure (Fin (t+1) → CovState)
  | 0 => Measure.dirac (fun _ => embed (1 : Mat n))
  | t+1 => (trajectoryLaw n t).bind (fun h =>
      (covStep (n-t) (h (Fin.last t))).map (fun S => Fin.lastCases S h))

/-- Residual column from the actual GEPP execution, as a total infinite vector. -/
noncomputable def actualColumn {n : ℕ} (A : Mat n) (t : ℕ) : ℕ → ℝ :=
  fun i => if hi : i+t < n then if ht : t < n then
    (run A t).matrix ⟨i+t,hi⟩ ⟨t,ht⟩ else 0 else 0

/-- Actual covariance computed from the actual previous pivot columns. -/
noncomputable def actualCov {n : ℕ} (A : Mat n) : ℕ → CovState
  | 0 => embed (1 : Mat n)
  | t+1 => stateUpdate (n-t) (actualCov A t) (actualColumn A t)

/-- The exact conditional-law integral identity given the first t original columns.
Testing all measurable events avoids conditioning on single histories of probability zero. -/
noncomputable def HasResidualLaw (n t : ℕ) (ht : t ≤ n) : Prop :=
  (∃ c : Matrix (Fin n) (Fin t) ℝ → CovState,
    Measurable c ∧ ∀ A, c (firstColumns ht A) = actualCov A t) ∧
  ∀ (H : Set (Matrix (Fin n) (Fin t) ℝ)) (E : Set (Mat (n-t))),
    MeasurableSet H → MeasurableSet E →
    GaussianMatrix.gaussianMatrix n n {A | firstColumns ht A ∈ H ∧ residual A t ∈ E} =
      ∫⁻ A in {A | firstColumns ht A ∈ H},
        columnsLaw (block (actualCov A t) (n-t)) (n-t) E
          ∂(GaussianMatrix.gaussianMatrix n n)

/-- Nd in Proposition 5.3 (d is the paper's d, so the initial dimension is d+1). -/
noncomputable def initialNormBound (n d : ℕ) : ℝ :=
  n / (Real.exp (1 + 1 / ((d:ℝ)+1)) * ((d:ℝ)+1+2*Real.log n))

end GEPPGrowth.Main


