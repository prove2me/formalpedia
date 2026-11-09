-- Prove2me | Definitions.Def_HarmonicKServer_Competitive_Framework
-- name    : HarmonicKServer_Competitive_Framework
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:12.542561+00:00
-- url     : https://prove2.me/theorems/0f906f25-6607-429c-980f-637e4251b393
-- title:
--   §2 — General server executions and conditional potential drift
-- statement:
--   A general randomized execution on a probability space records the requests, online and adversary configurations, and every charged service move. A pre-round sigma algebra is taken after adversary service and before the fresh online action. This representation allows arbitrary online service schedules and is independent of the Harmonic transition. The lazy predicate restricts only the adversary for the source's potential criterion.
--
--   For a finite real potential $\phi$, permutation invariance means that relabelling either tuple leaves its value unchanged. The adversary movement property is
--   $$\phi(X,Y')-\phi(X,Y)\le\rho\,d(y_i,y'_i).$$
--   The conditional online property is expressed without subtraction of infinite expectations: for every event $D$ known after adversary service,
--   $$\mathbb E[\mathbf1_D(c+\phi(X',Y))]\le\mathbb E[\mathbf1_D\phi(X,Y)].$$
--   For nonnegative potentials this is the conditional drift formulation of Property 2.2. Scalar costs and the potential observables have the measurability required for these expectations. Finite-horizon total costs are nonnegative extended integrals of the finite sums of charged distances. This layer supplies a criterion for every randomized algorithm's executions, including algorithms with non-finite action distributions.
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 3, §2 potential framework and Properties 2.1–2.2; Lemma 2.3 on p. 4 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Mathlib
import Definitions.Def_HarmonicKServer_Competitive_Harmonic

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- A general randomized server execution, with arbitrary online service schedules.
The pre-round sigma algebra includes completed adversary service and precedes online sampling.
Only real/nonnegative observables need measurability, not a discrete sigma algebra on V. -/
structure ServerExecution (k : ℕ) (V Ω : Type*) [MetricSpace V] [MeasurableSpace Ω]
    (μ : Measure Ω) (X₀ Y₀ : KServer.Config k V) where
  X : ℕ → Ω → KServer.Config k V
  Y : ℕ → Ω → KServer.Config k V
  request : ℕ → Ω → V
  advMoves : ℕ → Ω → Moves k V
  algMoves : ℕ → Ω → Moves k V
  pre : ℕ → MeasurableSpace Ω
  pre_le : ∀ t, pre t ≤ (inferInstance : MeasurableSpace Ω)
  pre_mono : Monotone pre
  startX : ∀ ω, X 0 ω = X₀
  startY : ∀ ω, Y 0 ω = Y₀
  advStep : ∀ t ω, Y (t+1) ω = execute (Y t ω) (advMoves t ω)
  algStep : ∀ t ω, X (t+1) ω = execute (X t ω) (algMoves t ω)
  advServes : ∀ t ω, Covers (Y (t+1) ω) (request t ω)
  algServes : ∀ t ω, Covers (X (t+1) ω) (request t ω)
  advCost_known : ∀ t, @Measurable Ω ℝ≥0∞ (pre t) inferInstance
    (fun ω => ENNReal.ofReal (travel (Y t ω) (advMoves t ω)))
  algCost_measurable : ∀ t, AEMeasurable
    (fun ω => ENNReal.ofReal (travel (X t ω) (algMoves t ω))) μ

def ExecutionLazy {k : ℕ} {V Ω : Type*} [MetricSpace V] [MeasurableSpace Ω]
    {μ : Measure Ω} {X₀ Y₀ : KServer.Config k V} (P : ServerExecution k V Ω μ X₀ Y₀) : Prop := by
  classical
  exact ∀ t ω, if Covers (P.Y t ω) (P.request t ω) then P.advMoves t ω = []
    else ∃ i, P.advMoves t ω = [(i, P.request t ω)]

def PermutationInvariant {k : ℕ} {V : Type*}
    (φ : KServer.Config k V → KServer.Config k V → ℝ) : Prop :=
  ∀ X Y (σ τ : Equiv.Perm (Fin k)), φ (X ∘ σ) (Y ∘ τ) = φ X Y

def AdversaryMovement {k : ℕ} {V : Type*} [MetricSpace V]
    (φ : KServer.Config k V → KServer.Config k V → ℝ) (ρ : ℝ) : Prop :=
  ∀ X Y i v, Function.Injective Y → Function.Injective (relocate Y i v) →
    φ X (relocate Y i v) - φ X Y ≤ ρ * dist (Y i) v

/-- Nonnegative conditional drift avoids subtracting infinite expectations. -/
def ConditionalOnlineMovement {k : ℕ} {V Ω : Type*} [MetricSpace V] [MeasurableSpace Ω]
    {μ : Measure Ω} {X₀ Y₀ : KServer.Config k V}
    (P : ServerExecution k V Ω μ X₀ Y₀)
    (φ : KServer.Config k V → KServer.Config k V → ℝ) : Prop :=
  (∀ t, @Measurable Ω ℝ≥0∞ (P.pre t) inferInstance
    (fun ω => ENNReal.ofReal (φ (P.X t ω) (P.Y t ω)))) ∧
  (∀ t, @Measurable Ω ℝ≥0∞ (P.pre t) inferInstance
    (fun ω => ENNReal.ofReal (φ (P.X t ω) (P.Y (t+1) ω)))) ∧
  (∀ t, AEMeasurable (fun ω => ENNReal.ofReal (φ (P.X (t+1) ω) (P.Y (t+1) ω))) μ) ∧
  ∀ t A, MeasurableSet[P.pre t] A →
    (∫⁻ ω in A, ENNReal.ofReal (travel (P.X t ω) (P.algMoves t ω)) +
      ENNReal.ofReal (φ (P.X (t+1) ω) (P.Y (t+1) ω)) ∂μ) ≤
    ∫⁻ ω in A, ENNReal.ofReal (φ (P.X t ω) (P.Y (t+1) ω)) ∂μ

noncomputable def executionOnlineCost {k : ℕ} {V Ω : Type*} [MetricSpace V] [MeasurableSpace Ω]
    {μ : Measure Ω} {X₀ Y₀ : KServer.Config k V}
    (P : ServerExecution k V Ω μ X₀ Y₀) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ t ∈ Finset.range N, ENNReal.ofReal (travel (P.X t ω) (P.algMoves t ω)) ∂μ

noncomputable def executionAdversaryCost {k : ℕ} {V Ω : Type*} [MetricSpace V] [MeasurableSpace Ω]
    {μ : Measure Ω} {X₀ Y₀ : KServer.Config k V}
    (P : ServerExecution k V Ω μ X₀ Y₀) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ t ∈ Finset.range N, ENNReal.ofReal (travel (P.Y t ω) (P.advMoves t ω)) ∂μ

end HarmonicKServer.Competitive


