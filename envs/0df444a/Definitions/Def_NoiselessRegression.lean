-- Prove2me | Definitions.Def_NoiselessRegression
-- name    : NoiselessRegression
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:20.105104+00:00
-- url     : https://prove2.me/theorems/d9244e0b-3798-49bf-86a7-b8721c372dd1
-- statement:
--   This block formalizes finite-memory learning of an unknown unit vector s in R^d from noiseless Gaussian linear observations, with accuracy measured by angle. Samples are T independent standard Gaussian vectors in R^d, and the label of a sample row x is exactly the inner product <x,s>, with no noise. uniformSphere(d) is the normalized surface measure on the unit sphere. A Learner with memory M (states are the 2^M elements of Fin(2^M)) over a randomness space Ω consists of an initial choice (a stop flag and a state), a transition map that, at step n and given the current state and the pair (row, label), returns a stop flag and a new state, and an output map that returns a unit vector from a step number and final state. The run reads rows in order, updating the state, and halts as soon as a stop flag is raised; the terminal pair records the stopping time (or T if it never stops) and state, and estimate outputs the unit vector chosen from that pair. Admissible requires almost-everywhere measurability of the initial choice, transition and output maps (with respect to the product of ρ and the reference measure Gaussian times Lebesgue), and of the estimate both for each fixed s and jointly with s uniform on the sphere. angularError(s,ŝ) is arccos<ŝ,s>. success(L,ρ,ε,s) is the probability, over ρ and the samples, that the angular error is at most ε, and uniformSuccess averages this event over s uniform on the sphere. SubquadraticMemory is a defined proposition, not an established theorem: there is a constant c>0 such that for every memory function M(d) that is o(d^2), there is a threshold d₀ so that for all d ≥ d₀, every T, every ε in (0,1/10], every probability measure ρ and every admissible learner with memory M(d) that either has uniform success at least 2/3 or has success at least 2/3 for every fixed s, must satisfy c·d·log(1/ε) ≤ T. FixedQuadraticMemory is likewise a defined proposition: for every A₀>0 there are c>0 and d₀ such that for all d ≥ d₀, all M ≤ A₀d^2, all T, ε in (0,1/10], and admissible learners with uniform success at least 2/3 (only the uniform-average hypothesis here), the same bound c·d·log(1/ε) ≤ T holds.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NoiselessRegression.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/NoiselessRegression.lean; bytes 16..4539
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
Finite-state Gaussian regression with noiseless labels and angular accuracy.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev UnitSphere (d : ℕ) := Metric.sphere (0 : Vector d) 1
abbrev State (M : ℕ) := Fin (2 ^ M)
abbrev Samples (d T : ℕ) := Fin T → Vector d

def uniformSphere (d : ℕ) : Measure (UnitSphere d) :=
  let σ := (volume : Measure (Vector d)).toSphere
  (σ Set.univ)⁻¹ • σ

def sampleLaw (d T : ℕ) : Measure (Samples d T) :=
  Measure.pi fun _ => stdGaussian (Vector d)

def observationReference (d : ℕ) : Measure (Vector d × ℝ) :=
  (stdGaussian (Vector d)).prod volume

structure Learner (d M T : ℕ) (Ω : Type u) where
  initialChoice : Ω → Bool × State M
  transition : ℕ → Ω → State M → (Vector d × ℝ) → Bool × State M
  output : ℕ → Ω → State M → UnitSphere d

namespace Learner

abbrev RunStatus (M : ℕ) := Sum (State M) (ℕ × State M)

def start {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω) (ω : Ω) :
    RunStatus M :=
  let a := L.initialChoice ω
  if a.1 then .inr (0, a.2) else .inl a.2

def run {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ → RunStatus M
  | 0 => L.start ω
  | n + 1 =>
    match L.run s ω x n with
    | .inr done => .inr done
    | .inl state =>
      if hn : n < T then
        let row := x ⟨n, hn⟩
        let a := L.transition (n + 1) ω state (row, ⟪row, s.val⟫)
        if a.1 then .inr (n + 1, a.2) else .inl a.2
      else .inl state

def terminal {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ × State M :=
  match L.run s ω x T with
  | .inl state => (T, state)
  | .inr done => done

def estimate {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : UnitSphere d :=
  let a := L.terminal s ω x
  L.output a.1 ω a.2

structure Admissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) : Prop where
  initialChoice : AEMeasurable L.initialChoice ρ
  transition : ∀ t a, AEMeasurable (fun z : Ω × (Vector d × ℝ) =>
    L.transition t z.1 a z.2) (ρ.prod (observationReference d))
  output : ∀ t a, AEMeasurable (fun ω => L.output t ω a) ρ
  fixed_experiment : ∀ s, AEMeasurable (fun z : Ω × Samples d T =>
    L.estimate s z.1 z.2) (ρ.prod (sampleLaw d T))
  uniform_experiment : AEMeasurable
    (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))

def angularError {d : ℕ} (s ŝ : UnitSphere d) : ℝ :=
  Real.arccos ⟪ŝ.val, s.val⟫

def success {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (s : UnitSphere d) : ℝ≥0∞ :=
  (ρ.prod (sampleLaw d T))
    {z | angularError s (L.estimate s z.1 z.2) ≤ ε}

def uniformSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) : ℝ≥0∞ :=
  ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))
    {z | angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}

end Learner

def SubquadraticMemory : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ) ^ 2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d (M d) T Ω, L.Admissible ρ →
    (((2 : ℕ) / (3 : ℕ) : ℝ≥0∞) ≤ L.uniformSuccess ρ ε ∨
      ∀ s, ((2 : ℕ) / (3 : ℕ) : ℝ≥0∞) ≤ L.success ρ ε s) →
    c * (d : ℝ) * Real.log (1 / ε) ≤ (T : ℝ)

def FixedQuadraticMemory : Prop :=
  ∀ A₀ : ℝ, 0 < A₀ → ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
    ∀ d : ℕ, d₀ ≤ d → ∀ M T : ℕ, (M : ℝ) ≤ A₀ * (d : ℝ) ^ 2 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d M T Ω, L.Admissible ρ →
    ((2 : ℕ) / (3 : ℕ) : ℝ≥0∞) ≤ L.uniformSuccess ρ ε →
    c * (d : ℝ) * Real.log (1 / ε) ≤ (T : ℝ)



end NoiselessRegression
end
end OAI


