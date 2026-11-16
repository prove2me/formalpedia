-- Prove2me | Definitions.Def_SingleCopyMoments_Adaptive_Supplement_Distributed
-- name    : SingleCopyMoments_Adaptive_Supplement_Distributed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:38:52.369203+00:00
-- url     : https://prove2.me/theorems/2d8f416b-1ce9-4a0d-9208-1e6df6cf1647
-- title:
--   One-way distributed protocols and alternating-moment success
-- statement:
--   Alice receives $n_A$ copies of $\rho$ and Bob receives $n_B$ copies of $\sigma$. An independent shared classical seed selects Alice's local joint POVM. Her classical outcome is sent to Bob and selects his local joint POVM and real readout. Both measurements have the exact normalized tensor-power Born kernels. Alice's effects never depend on the unknown states; Bob's effects depend only on the seed and message. The law is the composition of these kernels, without quantum communication or preshared entanglement.
--
--   The success predicate requires a normalized joint transcript law and a measurable event satisfying, for every pair of states,
--   $$\Pr\{|\widehat z-\operatorname{Tr}[(\rho\sigma)^t]|\le\epsilon\}\ge1-\delta.$$
--   The trace is real; the definition takes its real part. The deterministic allocation $n_A+n_B$ counts all copies supplied to local operations, including unused copies, failed filters, pilots and normalization trials. Local joint operations and retained local quantum outputs are allowed within each block POVM.
--
--   This operational model is separate from the single-copy model and contains no performance bound.
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Theorem 29 and §6.4, printed pp.30–32 (PDF pp.32–34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Supplement_JointMeasurements

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- One-way classical communication with arbitrary local joint POVMs. Alice's
classical record is the message. Each local quantum memory and local instrument can
be included in that party's block POVM; no quantum system crosses between parties. -/
structure OneWayProtocol (d nA nB : ℕ) where
  Seed : Type
  Message : Type
  Outcome : Type
  seedMS : MeasurableSpace Seed
  messageMS : MeasurableSpace Message
  outcomeMS : MeasurableSpace Outcome
  seedLaw : @Measure Seed seedMS
  seed_probability : @IsProbabilityMeasure Seed seedMS seedLaw
  alice : letI := messageMS; Seed → BlockMeasurement d nA Message
  aliceStep : letI := seedMS; letI := messageMS; Kernel (State d × Seed) Message
  alice_markov : letI := seedMS; letI := messageMS; IsMarkovKernel aliceStep
  alice_eq : letI := seedMS; letI := messageMS;
    ∀ (ρ : State d) z, aliceStep (ρ,z) = (alice z).sample ρ
  bob : letI := outcomeMS; Seed × Message → BlockMeasurement d nB Outcome
  bobStep : letI := seedMS; letI := messageMS; letI := outcomeMS;
    Kernel (State d × (Seed × Message)) Outcome
  bob_markov : letI := seedMS; letI := messageMS; letI := outcomeMS; IsMarkovKernel bobStep
  bob_eq : letI := seedMS; letI := messageMS; letI := outcomeMS;
    ∀ (σ : State d) H, bobStep (σ,H) = (bob H).sample σ
  output : Seed × Message × Outcome → ℝ
  measurable_output : letI := seedMS; letI := messageMS; letI := outcomeMS; Measurable output

attribute [instance] OneWayProtocol.seedMS OneWayProtocol.messageMS OneWayProtocol.outcomeMS

def oneWayLaw {d nA nB : ℕ} (P : OneWayProtocol d nA nB) (ρ σ : State d) :
    Measure (P.Seed × P.Message × P.Outcome) :=
  P.seedLaw.bind (fun z => (P.aliceStep (ρ,z)).bind (fun m =>
    (P.bobStep (σ,(z,m))).map (fun y => (z,m,y))))

def alternatingMoment {d : ℕ} (ρ σ : State d) (t : ℕ) : ℝ :=
  ((ρ.val * σ.val) ^ t).trace.re

def DistributedSucceeds {d nA nB : ℕ} (P : OneWayProtocol d nA nB)
    (t : ℕ) (ε δ : ℝ) : Prop :=
  ∀ ρ σ : State d, IsProbabilityMeasure (oneWayLaw P ρ σ) ∧
    MeasurableSet {H | |P.output H - alternatingMoment ρ σ t| ≤ ε} ∧
    ENNReal.ofReal (1 - δ) ≤ (oneWayLaw P ρ σ)
      {H | |P.output H - alternatingMoment ρ σ t| ≤ ε}

end SingleCopyMoments.Adaptive.Supplement


