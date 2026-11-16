-- Prove2me | Definitions.Def_SingleCopyMoments_Adaptive_Supplement_Multisource
-- name    : SingleCopyMoments_Adaptive_Supplement_Multisource
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:37:19.034293+00:00
-- url     : https://prove2.me/theorems/3a312743-3246-45ac-b42c-8549f3309699
-- title:
--   Multisource adaptive single-copy protocols and ordered complex overlap
-- statement:
--   For $m$ unknown states $\rho_0,\ldots,\rho_{m-1}$ on $\mathbb C^d$, a multisource protocol has an input-independent probability seed. In each round it selects a source by a measurable classical rule and applies a single-copy POVM; the selection and effects depend only on the seed and earlier outcomes. The transcript law is the recursion of the selected state's Born transition. A run of $T$ rounds consumes $T$ copies in total across all sources, with failures counted. Source selections are reconstructible classical functions of the recorded seed and outcomes.
--
--   The complex readout estimates the ordered overlap
--   $$ z=\operatorname{Tr}(\rho_0\rho_1\cdots\rho_{m-1}),\qquad
--      \Pr\{|\widehat z-z|\le\epsilon\}\ge1-\delta.$$
--   Success requires a normalized law and a measurable event for every input vector. Arbitrary measurable outcome spaces, equal input states and both components of the complex output are allowed. No quantum information passes from one original copy to another.
--
--   This extends the published POVM model with classical source selection and a complex readout; it assumes no accuracy or copy bound.
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), §5.4 and Theorem 25, printed pp.19–20, 27–28 (PDF pp.21–22, 29–30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Estimation

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- The source selector and the POVM read only classical data. The input vector is
used only by the Born kernel, never by the selector, measurement, or readout. -/
structure MultiProtocol (d m : ℕ) where
  Seed : Type
  Outcome : Type
  seedMS : MeasurableSpace Seed
  outcomeMS : MeasurableSpace Outcome
  seedLaw : @Measure Seed seedMS
  seed_probability : @IsProbabilityMeasure Seed seedMS seedLaw
  source : Seed × (ℕ → (Unit ⊕ Outcome)) → ℕ → Fin m
  measurable_source : letI := seedMS; letI := outcomeMS;
    ∀ i, Measurable (fun H => source H i)
  measurement : letI := outcomeMS;
    ℕ → Seed × (ℕ → (Unit ⊕ Outcome)) → IncoherentPurity.Adaptive.POVM d Outcome
  step : letI := seedMS; letI := outcomeMS;
    ℕ → Kernel ((Fin m → State d) × (Seed × (ℕ → (Unit ⊕ Outcome)))) Outcome
  step_markov : letI := seedMS; letI := outcomeMS; ∀ i, IsMarkovKernel (step i)
  step_eq : letI := seedMS; letI := outcomeMS;
    ∀ i (ρ : Fin m → State d) H,
      step i (ρ,H) = (measurement i H).born (ρ (source H i))
  output : Seed × (ℕ → (Unit ⊕ Outcome)) → ℂ
  measurable_output : letI := seedMS; letI := outcomeMS; Measurable output

attribute [instance] MultiProtocol.seedMS MultiProtocol.outcomeMS

abbrev MultiRecord {d m : ℕ} (P : MultiProtocol d m) :=
  P.Seed × (ℕ → (Unit ⊕ P.Outcome))

/-- T recursive Born transitions, hence exactly T original copies in total. -/
def multiLaw {d m : ℕ} (P : MultiProtocol d m) (ρ : Fin m → State d) :
    ℕ → Measure (MultiRecord P)
  | 0 => P.seedLaw.map (fun z => (z, fun _ => Sum.inl ()))
  | i+1 => (multiLaw P ρ i).bind (fun H =>
      (P.step i (ρ,H)).map (fun y =>
        (H.1, fun j => if j = i then Sum.inr y else H.2 j)))

/-- Matrix product in the prescribed input order, not its symmetrization. -/
def cyclicOverlap {d m : ℕ} (ρ : Fin m → State d) : ℂ :=
  ((List.ofFn fun j => (ρ j).val).prod).trace

def OverlapSucceeds {d m : ℕ} (P : MultiProtocol d m) (T : ℕ) (ε δ : ℝ) : Prop :=
  ∀ ρ : Fin m → State d, IsProbabilityMeasure (multiLaw P ρ T) ∧
    MeasurableSet {H | ‖P.output H - cyclicOverlap ρ‖ ≤ ε} ∧
    ENNReal.ofReal (1 - δ) ≤ (multiLaw P ρ T) {H | ‖P.output H - cyclicOverlap ρ‖ ≤ ε}

end SingleCopyMoments.Adaptive.Supplement


