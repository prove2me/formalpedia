-- Prove2me | Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
-- name    : StabilityDichotomies_Approximability_BijunctiveLaw
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T07:45:49.946265+00:00
-- url     : https://prove2.me/theorems/4231e7d9-c1d9-465d-9f58-a09087d4d84e
-- title:
--   Product-measure output law for the bijunctive priority-and-shift algorithm
-- statement:
--   The input seed measure is the independent product of one uniform [0,1] priority per constraint occurrence, one uniform cutoff on [1−ε/2,1], and one exponential shift per literal at rate β=ε/(2bΓ). The output-law relation equates a semantic solver’s assignment masses with the seed measure of the corresponding output events under the deterministic core of Definition 4.8. Uniform measures are conditional Lebesgue measures and the exponential measure is Mathlib’s rate-parametrized exponential law. The definition does not itself prove probability normalization, output-event measurability, existence of a matching solver, the upper bounds, or executable runtime.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Definition 4.8, p. 19, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive

noncomputable section
open scoped Classical BigOperators ENNReal
open MeasureTheory
namespace StabilityDichotomies.Bijunctive
open StabilityDichotomies.Solvability

/-- Uniform measure on [0,1] for one occurrence priority. -/
def unitPriorityMeasure : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc (0 : ℝ) 1)

/-- Uniform cutoff measure on [1-ε/2,1], for 0 < ε ≤ 1. -/
def cutoffMeasure (ε : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc (1 - ε / 2) 1)

/-- Rate-β exponential measure on [0,∞), for β > 0. -/
def shiftMeasure (β : ℝ) : Measure ℝ :=
  ProbabilityTheory.expMeasure β

/-- Independent product of all occurrence priorities, the common cutoff, and all literal shifts. -/
def bijunctiveSeedMeasure {Γ : Language} {V : Type} [Fintype V] (rep : TwoCNFRepresentation Γ)
    (I : Instance Γ V) (ε : ℝ) : Measure ((Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)) :=
  (Measure.pi fun _ : Fin I.constraints.card => unitPriorityMeasure).prod
    ((cutoffMeasure ε).prod (Measure.pi fun _ : Literal V => shiftMeasure (bijunctiveRate rep ε)))

/-- Exact Definition 4.8 output-law relation. This does not by itself assert normalization,
measurability, existence of a matching solver, or computational runtime. -/
def BijunctiveOutputLaw (Γ : Language) (rep : TwoCNFRepresentation Γ) (ε : ℝ) (A : Solver Γ) : Prop :=
  ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I → ∀ x : V → Bool,
    (A V I x).toReal = (bijunctiveSeedMeasure rep I ε
      {seed | bijunctiveOutput rep I ε seed.1 seed.2.1 seed.2.2 = x}).toReal

end StabilityDichotomies.Bijunctive


