-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P51
-- name    : QAlgorithms_Papers_Independent_Intake100_P51
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T13:41:02.111365+00:00
-- url     : https://prove2.me/theorems/5aadcc88-4357-4ebf-b8d4-6819378158a9
-- title:
--   Definitions for The Degraded Poisson Wiretap Channel
-- statement:
--   The objects the formalized statements of *The Degraded Poisson Wiretap Channel* (arXiv:1004.0269) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `conditionalEvent`: PDF pp.5,19: conditional probability of an event given the entire random object X, defined by conditional expectation of its indicator. In all uses, X and the event are measurable and mu is a probability measure, so the indicator is integrable and the conditioning sigma algebra is a subalgebra.
--   - `ConditionallyIndependent`: PDF pp.5,18–19: conditional independence given sigma(X), tested on every pair of measurable output events. This conditional-expectation formulation works on arbitrary probability spaces and imposes no standard-Borel assumption on the underlying sample space.
--   - `gaussianJoint`: PDF p.4: independent input and independent centered Gaussian noises. The two variance parameters are N1*B and N2*B, rather than their square roots. Only positive bandwidth and noise parameters are used in the limit theorem.
--   - `gaussianInformationDifference`: PDF pp.4–5: the actual scalar Gaussian wiretap information difference. Under the power and positive-noise assumptions in gaussianSecrecyValue, both information terms are finite (bounded by the scalar Gaussian capacity), which justifies the real subtraction. The observations share the first noise.
--   - `gaussianSecrecyValue`: PDF pp.5–6: the variational finite-bandwidth value used by the source, with 2*B scalar channel uses per second. For B>0, P>=0 and N1,N2>0 the set is nonempty (the point mass at zero is admissible) and bounded above by the Gaussian main-channel capacity. The second moment must be integrable; otherwise Lean's totalized integral would admit inputs of infinite power.
-- source:
--   The Degraded Poisson Wiretap Channel, arXiv:1004.0269v1, https://arxiv.org/abs/1004.0269v1

import Mathlib

/-!
Statements from Laourine and Wagner, arXiv:1004.0269v1, PDF pp.4–6,18–19.
The source's operational Poisson results are deferred in the assigned HARD.md;
no analytic expression is substituted for an operational capacity definition.
Information is classical, uses natural logarithms, and retains infinite values.
Compilation is pending the authorized batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P51

open MeasureTheory Filter
open InformationTheory (klDiv)
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF pp.5,19: conditional probability of an event given the entire random
object X, defined by conditional expectation of its indicator. In all uses,
X and the event are measurable and mu is a probability measure, so the
indicator is integrable and the conditioning sigma algebra is a subalgebra. -/
def conditionalEvent {Omega A : Type*} [MeasurableSpace Omega]
    [MeasurableSpace A] (mu : Measure Omega) (X : Omega → A)
    (s : Set Omega) : Omega → ℝ :=
  MeasureTheory.condExp (MeasurableSpace.comap X inferInstance) mu
    (s.indicator (fun _ => (1 : ℝ)))

/-- PDF pp.5,18–19: conditional independence given sigma(X), tested on every
pair of measurable output events. This conditional-expectation formulation
works on arbitrary probability spaces and imposes no standard-Borel assumption
on the underlying sample space. -/
def ConditionallyIndependent {Omega A B C : Type*} [MeasurableSpace Omega]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (mu : Measure Omega) (X : Omega → A) (Y : Omega → B) (Z : Omega → C) : Prop :=
  ∀ (s : Set B) (t : Set C), MeasurableSet s → MeasurableSet t →
    conditionalEvent mu X (Y ⁻¹' s ∩ Z ⁻¹' t) =ᵐ[mu]
      (fun omega => conditionalEvent mu X (Y ⁻¹' s) omega *
        conditionalEvent mu X (Z ⁻¹' t) omega)

/-- Sanity: one deterministic, normalized observation has no mutual information. -/
example : klDiv ((Measure.dirac ()).map (fun x : Unit => (x, x)))
    (((Measure.dirac ()).map (fun x : Unit => x)).prod
      ((Measure.dirac ()).map (fun x : Unit => x))) = 0 := by
  simp [Measure.dirac_prod_dirac]

/-- Sanity: the impossible event has conditional probability zero. -/
example {Omega A : Type*} [MeasurableSpace Omega] [MeasurableSpace A]
    (mu : Measure Omega) (X : Omega → A) :
    conditionalEvent mu X ∅ = 0 := by
  funext omega
  simp [conditionalEvent, MeasureTheory.condExp_zero]

/-- PDF p.4: independent input and independent centered Gaussian noises.
The two variance parameters are N1*B and N2*B, rather than their square roots.
Only positive bandwidth and noise parameters are used in the limit theorem. -/
def gaussianJoint (B N1 N2 : ℝ) (input : Measure ℝ) : Measure (ℝ × (ℝ × ℝ)) :=
  input.prod ((ProbabilityTheory.gaussianReal 0 (Real.toNNReal (N1 * B))).prod
    (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (N2 * B))))

/-- PDF pp.4–5: the actual scalar Gaussian wiretap information difference.
Under the power and positive-noise assumptions in gaussianSecrecyValue,
both information terms are finite (bounded by the scalar Gaussian capacity),
which justifies the real subtraction. The observations share the first noise. -/
def gaussianInformationDifference (B N1 N2 : ℝ) (input : Measure ℝ) : ℝ :=
  let mu := gaussianJoint B N1 N2 input
  (klDiv (mu.map (fun p => (p.1, p.1 + p.2.1)))
    ((mu.map (fun p => p.1)).prod (mu.map (fun p => p.1 + p.2.1)))).toReal -
  (klDiv (mu.map (fun p => (p.1, p.1 + p.2.1 + p.2.2)))
    ((mu.map (fun p => p.1)).prod
      (mu.map (fun p => p.1 + p.2.1 + p.2.2)))).toReal

/-- PDF pp.5–6: the variational finite-bandwidth value used by the source,
with 2*B scalar channel uses per second. For B>0, P>=0 and N1,N2>0 the
set is nonempty (the point mass at zero is admissible) and bounded above by
the Gaussian main-channel capacity. The second moment must be integrable;
otherwise Lean's totalized integral would admit inputs of infinite power. -/
def gaussianSecrecyValue (B P N1 N2 : ℝ) : ℝ :=
  2 * B * sSup {r : ℝ | ∃ input : Measure ℝ,
    IsProbabilityMeasure input ∧ Integrable (fun x : ℝ => x ^ 2) input ∧
    (∫ x : ℝ, x ^ 2 ∂input) ≤ P ∧
    r = gaussianInformationDifference B N1 N2 input}

/-- Sanity: at bandwidth zero, all three deterministic zero coordinates
have their normalized joint point-mass law. The limit only uses B>0. -/
example (N1 N2 : ℝ) : gaussianJoint 0 N1 N2 (Measure.dirac 0) =
    Measure.dirac (0, (0, 0)) := by
  simp [gaussianJoint, Real.toNNReal_zero, ProbabilityTheory.gaussianReal_zero_var,
    Measure.dirac_prod_dirac]

end QAlgorithms.Papers.Independent.Intake100.P51


