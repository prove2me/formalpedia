-- Prove2me | Definitions.Def_FreeProbAMP_StateEvolution_History
-- name    : FreeProbAMP_StateEvolution_History
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:26:43.35479+00:00
-- url     : https://prove2.me/theorems/a66b8971-fed7-4060-bcf2-af375ceedaba
-- title:
--   Alternating observation histories, conditional laws and Onsager residuals
-- statement:
--   Starting with $\mathcal F_0=\sigma(u^0)$ independent of $A$, an alternating observation scheme chooses $q^t$ measurable for $\mathcal F_t$, reveals $y^t=Aq^t$, forms $\mathcal G_t=\mathcal F_t\vee\sigma(y^t)$, chooses a $\mathcal G_t$-measurable symmetric $r^t$, and reveals $x^t=A^*r^t$ to obtain $\mathcal F_{t+1}$.
--
--   Equality of conditional laws given $\mathcal H$ means, for every $\mathcal H$-measurable event $C$ and measurable target set $S$,
--
--   $$\mathbb P(C\cap\{X\in S\})=\mathbb P(C\cap\{Y\in S\}).$$
--
--   A conditional law $K(\omega)$ is specified by replacing the right side with $\int_C K(\omega,S)\,d\mathbb P$. These are distributional assertions, rather than equality between independent samples. Conditional tightness is expressed by bounds on all conditioning events, with thresholds chosen for each error probability before the dimension.
--
--   For AMP use $q^t=m^t,r^t=M^t$. With columns $Q=(m^0,\ldots,m^{t-1})$, $R=(M^0,\ldots,M^{t-1})$, $X=A^*R$, define
--
--   $$\beta_t=(Q^*Q)^{-1}Q^*m^t,\qquad h^t=m^t-Q\beta_t,$$
--   $$ (d_k^{(t)})_r=\mathbf1_{r<k}d_{k,r+1},\qquad
--   \delta_t=d_t^{(t)}-\sum_{k<t}(\beta_t)_k d_k^{(t)}.$$
--
--   The vector and matrix cancellation errors are the differences in (6.9) and (6.10). These are built from the actual observations. Empty histories are genuine zero column maps. Matrix inversion is total in Lean, but almost-sure finite-rank conclusions and eventual limiting positivity justify it in applications without adding rank assumptions to the goal.
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), pp. 22–23, (4.3)–(4.7); pp. 31–32, (6.4)–(6.8)

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_Limit

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

variable {Ω : Type*} [MeasurableSpace Ω]

abbrev sigma {X : Type*} [MeasurableSpace X] (f : Ω → X) : MeasurableSpace Ω :=
  MeasurableSpace.comap f inferInstance

/-- Equality of conditional laws, tested jointly with every event in the conditioning sigma-field. -/
def CondSameLaw {X : Type*} [MeasurableSpace X] (μ : Measure Ω)
    (H : MeasurableSpace Ω) (f g : Ω → X) : Prop :=
  AEMeasurable f μ ∧ AEMeasurable g μ ∧ ∀ C S, MeasurableSet[H] C → MeasurableSet S →
    μ (C ∩ f ⁻¹' S) = μ (C ∩ g ⁻¹' S)

/-- A conditional law specified by a probability-measure-valued function. -/
def ConditionalLaw {X : Type*} [MeasurableSpace X] (μ : Measure Ω)
    (H : MeasurableSpace Ω) (f : Ω → X) (K : Ω → Measure X) : Prop :=
  AEMeasurable f μ ∧ ∀ C S, MeasurableSet[H] C → MeasurableSet S →
    μ (C ∩ f ⁻¹' S) = ∫⁻ ω in C, K ω S ∂μ

/-- Uniform conditional tightness, expressed as bounds on every conditioning event. -/
def ConditionalOP (μ : Measure Ω) (H : ℕ → MeasurableSpace Ω)
    (X scale : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 < L ∧ ∃ d₀ : ℕ, ∀ d, d₀ ≤ d →
    ∀ C, MeasurableSet[H d] C →
      μ (C ∩ {ω | L * scale d ω < X d ω}) ≤ ENNReal.ofReal ε * μ C

structure Observation (Ω : Type*) [MeasurableSpace Ω] (n d : ℕ) where
  A : Ω → Fin n → RMat d
  seed : Ω → Fin n → ℝ
  q : ℕ → Ω → Fin n → ℝ
  r : ℕ → Ω → RMat d

namespace Observation

def y {n d : ℕ} (O : Observation Ω n d) (t : ℕ) (ω : Ω) : RMat d := applyA (O.A ω) (O.q t ω)
def x {n d : ℕ} (O : Observation Ω n d) (t : ℕ) (ω : Ω) : Fin n → ℝ := applyAdj (O.A ω) (O.r t ω)

abbrev F {n d : ℕ} (O : Observation Ω n d) (t : ℕ) : MeasurableSpace Ω :=
  sigma O.seed ⊔ ⨆ j : Fin t, sigma (O.y j) ⊔ sigma (O.x j)
abbrev G {n d : ℕ} (O : Observation Ω n d) (t : ℕ) : MeasurableSpace Ω := O.F t ⊔ sigma (O.y t)

def Adaptive {n d : ℕ} (O : Observation Ω n d) (μ : Measure Ω) (T : ℕ) : Prop :=
  Measurable O.seed ∧ Indep (sigma O.seed) (sigma O.A) μ ∧
  (∀ t, t ≤ T → Measurable[O.F t] (O.q t) ∧ Measurable[O.G t] (O.r t)) ∧
  (∀ t, t ≤ T → ∀ᵐ ω ∂μ, (O.r t ω).transpose = O.r t ω)

end Observation

namespace FiniteData

def observations (D : FiniteData Ω) (d : ℕ) : Observation Ω (D.n d) (d+1) :=
  ⟨D.A d, D.u₀ d, fun t => D.m t d, fun t => D.M t d⟩

end FiniteData

/-- The actual coefficient and residual definitions (6.4)–(6.8). -/
def historyBeta (D : FiniteData Ω) (t d : ℕ) (ω : Ω) : Fin t → ℝ :=
  let Q := fun s : Fin t => D.m s d ω
  (gram vecInner Q)⁻¹ *ᵥ adjColumns vecInner Q (D.m t d ω)

def historyResidual (D : FiniteData Ω) (t d : ℕ) (ω : Ω) : Fin (D.n d) → ℝ :=
  D.m t d ω - columns (fun s : Fin t => D.m s d ω) (historyBeta D t d ω)

def shiftedDerivs (D : FiniteData Ω) (t k d : ℕ) (ω : Ω) : Fin t → ℝ :=
  fun r => if h : r.val < k then
    avg (D.n d) (fun i => derivCoord (D.g k) ⟨r.val+1, by omega⟩ (D.inputs k d ω i)) else 0

def historyDelta (D : FiniteData Ω) (t d : ℕ) (ω : Ω) : Fin t → ℝ :=
  shiftedDerivs D t t d ω - ∑ k : Fin t, (historyBeta D t d ω k) • shiftedDerivs D t k d ω

def cancellationVector (D : FiniteData Ω) (t d : ℕ) (ω : Ω) : Fin t → ℝ :=
  let R := fun r : Fin t => D.M r d ω
  adjColumns vecInner (fun r => applyAdj (D.A d ω) (R r)) (historyResidual D t d ω) -
    D.α d • ((gram matInner R) *ᵥ historyDelta D t d ω)

def cancellationMatrix (D : FiniteData Ω) (t d : ℕ) (ω : Ω) : RMat (d+1) :=
  let R := fun r : Fin t => D.M r d ω
  let X := fun r : Fin t => applyAdj (D.A d ω) (R r)
  columns R ((gram matInner R)⁻¹ *ᵥ adjColumns vecInner X (historyResidual D t d ω)) -
    D.α d • columns R (historyDelta D t d ω)

end FreeProbAMP.StateEvolution


