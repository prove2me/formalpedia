-- Prove2me | Definitions.Def_QuantumWork1289_Metering_oracleExperiment
-- name    : QuantumWork1289_Metering_oracleExperiment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T04:37:59.183917+00:00
-- url     : https://prove2.me/theorems/95f05f66-bf20-4d77-bfca-7ec092803d93
-- title:
--   Full random-oracle experiment and YZ acceptance
-- statement:
--   The oracle $f:X\to B$ is sampled once from the full product of uniform answer laws. Repeated addresses use the same sampled answer. This definition does not truncate $X$.
--
--   An independent seed $\omega$ with probability law $\mu$ jointly specifies the initial quantum advice, private randomness, program and side resources. Those quantities may be correlated with one another. The oracle is independent of their entire joint specification because the experiment uses the product law $\mu\otimes\operatorname{Law}(f)$. Quantum branch probabilities are calculated by the hybrid execution.
--
--   For an acceptance predicate $V$ the eventual success probability is
--
--   $$\sup_{t\in\mathbb N}\int P[\text{an accepted output has halted by horizon }t\mid\omega,f]\,d(\mu\otimes\operatorname{Law}(f)).$$
--
--   The finite-horizon integrand is the sum of the actual accepted branch traces; timeout and abort reject. Measurable execution means precisely that these integrands are almost everywhere measurable. Extended nonnegative integrals and suprema preserve the probability interpretation without undefined real-integral or real-supremum defaults.
--
--   For the Boolean YZ experiment, an output $(\eta,w)$ is accepted exactly when
--
--   $$w\in\mathcal C\quad\text{and}\quad f(\eta,i,w_i)=0\ \text{for every }i\in[N].$$
--
--   An optional output explicitly represents abort. This layer supplies the common probability experiment, rather than accepting a success probability as input.
-- source:
--   Mohammed Barhoush, Proof of Quantum Work with Classical Verification, STOC 2027 submission #1289 (October 2026), pp. 12–14, oracle independence and security experiment; pp. 18–22, Theorem 4

import Mathlib
import Definitions.Def_QuantumWork1289_Metering_hybridMachine
set_option autoImplicit false

open scoped ENNReal

namespace QuantumWork1289.Metering

open MeasureTheory

/-- Independent uniform answers on the entire domain, sampled once and reused.
The finite answer alphabet has its discrete measurable structure. -/
noncomputable def oracleLaw (X B : Type) [Fintype B] [Nonempty B]
    [MeasurableSpace B] : Measure (X → B) :=
  Measure.infinitePi fun _ : X => (PMF.uniformOfFintype B).toMeasure

/-- The same seed fixes all initial advice, private randomness and independent side resources.
It is sampled independently of the entire oracle. Branch measurements are in execute. -/
structure SeededMachine (X B O Ω S : Type) (n : ℕ) where
  machine : Ω → HybridMachine X B O S n
  initialState : Ω → InitialState n

/-- Probability of eventual acceptance, by monotone finite horizons, under the independent
seed/oracle product law. No real-valued integral can default to zero here. -/
noncomputable def successProbability {X B O Ω S : Type} [Fintype B] [Nonempty B]
    [DecidableEq B] [AddCommGroup B] [MeasurableSpace B] [MeasurableSpace Ω]
    {n : ℕ} (A : SeededMachine X B O Ω S n) (μ : Measure Ω)
    (accept : (X → B) → O → Prop) : ℝ≥0∞ :=
  ⨆ t : ℕ, ∫⁻ p : Ω × (X → B),
    acceptedMass (A.machine p.1) (A.initialState p.1) accept t p.2
      ∂(μ.prod (oracleLaw X B))

/-- Ordinary measurability of the computed finite-horizon probabilities. This is a stochastic
well-posedness condition, with no success bound, degree certificate or listing certificate. -/
def MeasurableExecution {X B O Ω S : Type} [Fintype B] [Nonempty B]
    [DecidableEq B] [AddCommGroup B] [MeasurableSpace B] [MeasurableSpace Ω]
    {n : ℕ} (A : SeededMachine X B O Ω S n) (μ : Measure Ω)
    (accept : (X → B) → O → Prop) : Prop :=
  ∀ t : ℕ, AEMeasurable (fun p : Ω × (X → B) =>
    acceptedMass (A.machine p.1) (A.initialState p.1) accept t p.2)
    (μ.prod (oracleLaw X B))

/-- The Boolean YZ acceptance event, with abort explicitly rejecting. -/
def yzAccept {E Γ : Type} {N : ℕ} (code : Set (Fin N → Γ))
    (f : (E × Fin N × Γ) → Bool) (out : Option (E × (Fin N → Γ))) : Prop :=
  match out with
  | none => False
  | some (η, w) => w ∈ code ∧ ∀ i, f (η, i, w i) = false

end QuantumWork1289.Metering


