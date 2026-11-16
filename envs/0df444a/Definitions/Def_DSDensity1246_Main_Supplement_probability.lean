-- Prove2me | Definitions.Def_DSDensity1246_Main_Supplement_probability
-- name    : DSDensity1246_Main_Supplement_probability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:23:11.009202+00:00
-- url     : https://prove2.me/theorems/fe2d76cc-37d7-4ff5-8fc9-06c83b1caeae
-- title:
--   Population error, realizability, and general independent sampling
-- statement:
--   Let D be any probability distribution on the labeled data space X×Y, carrying its σ-algebra as part of the law. The population error of a single-label hypothesis h and its class benchmark are
--
--   $$\operatorname{err}_D(h)=D\{(x,y):h(x)\ne y\},\qquad b_D(H)=\inf_{h\in H}\operatorname{err}_D(h).$$
--
--   Realizability means b_D(H)=0, without requiring that one hypothesis attain error zero. Sampling m observations uses the genuine finite product distribution D^m. A seed distribution ρ is combined with the sample by the product law D^m⊗ρ; it is independent of the data.
--
--   These definitions provide the probability model shared by every learning statement. They neither restrict D to discrete distributions nor supply event probabilities as independent oracle values.
--
--   **Formalization Note** A data law is a dependent pair of a Mathlib σ-algebra and a Mathlib probability measure on it; lower bounds may choose both, rather than being forced into an externally fixed σ-algebra. Arbitrary events are evaluated by the associated outer measure; for measurable events this is ordinary probability. Errors and the infimum lie in [0,∞], with the empty-class infimum equal to infinity, so an empty class is never realizable. The empty sample has its usual unit-mass product law. No hypothesis or learner measurability assumption is added.
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), pp. 12–13, §3 and Definition 1

import Mathlib

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DSDensity1246.Main.Supplement

/-- A probability law on an arbitrary carrier includes its σ-algebra. In particular,
existential hard distributions are not restricted to an externally fixed σ-algebra. -/
def DataLaw (Z : Type*) := (s : MeasurableSpace Z) × @ProbabilityMeasure Z s

/-- §3, p.12: single-label population error. Applying a measure to an arbitrary
set means its outer probability; no hypothesis measurability is assumed. -/
noncomputable def hypothesisError {X Y : Type*}
    (D : DataLaw (X × Y)) (h : X → Y) : ℝ≥0∞ :=
  letI : MeasurableSpace (X × Y) := D.1
  (D.2 : Measure (X × Y)) {z | h z.1 ≠ z.2}

/-- §3: the comparator is the best SINGLE hypothesis; the empty infimum is ⊤. -/
noncomputable def bestError {X Y : Type*}
    (D : DataLaw (X × Y)) (H : Set (X → Y)) : ℝ≥0∞ :=
  ⨅ h : H, hypothesisError D h.1

/-- §3: realizability is infimum zero, without an attainment assumption. -/
def Realizable {X Y : Type*} (D : DataLaw (X × Y)) (H : Set (X → Y)) : Prop :=
  bestError D H = 0

/-- The genuine iid law on indexed samples, including the unique empty sample. -/
noncomputable def iidLaw {Z : Type*} (D : DataLaw Z) (m : ℕ) :
    letI : MeasurableSpace Z := D.1
    Measure (Fin m → Z) :=
  letI : MeasurableSpace Z := D.1
  Measure.pi (fun _ : Fin m => (D.2 : Measure Z))

/-- Independent training data and learner seed, with arbitrary lawful seed distribution. -/
noncomputable def trainingLaw {Z R : Type*} [MeasurableSpace R]
    (D : DataLaw Z) (ρ : ProbabilityMeasure R) (m : ℕ) :
    letI : MeasurableSpace Z := D.1
    Measure ((Fin m → Z) × R) :=
  letI : MeasurableSpace Z := D.1
  (iidLaw D m).prod (ρ : Measure R)

end DSDensity1246.Main.Supplement


