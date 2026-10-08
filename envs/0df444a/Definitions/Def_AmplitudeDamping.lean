-- Prove2me | Definitions.Def_AmplitudeDamping
-- name    : AmplitudeDamping
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:00.093543+00:00
-- url     : https://prove2.me/theorems/7d9d5eed-379c-472f-902f-8671d00adecd
-- statement:
--   For n qubits, matrices are indexed by binary strings of length n; a state is a positive semidefinite matrix of trace one, and its entropy is Tr(−P log P), using spectral functional calculus and 0 log 0=0. For real parameters γ and ν, the four single-qubit Kraus matrices are A₀=diag(√(1−ν),√(1−ν)√(1−γ)), A₁ with sole nonzero entry √(γ(1−ν)) in position (0,1), A₂=diag(√ν√(1−γ),√ν), and A₃ with sole nonzero entry √(γν) in position (1,0). The n-use map Φₙ(P) sums KᵣPKᵣ* over every length-n string r of Kraus indices, where Kᵣ is the tensor product of the corresponding A matrices. These formulas are defined for all real parameters, without an imposed physical parameter range. A finite ensemble consists of arbitrary n-qubit states with nonnegative weights summing to one. Its Holevo value is the entropy of the average output minus the average output entropy, divided by ln 2; holevo(γ,ν,n) is the supremum over all such ensembles. An n-use code has a positive number M of messages, arbitrary state encodings, and one collective decoding measurement comprising positive semidefinite matrices Dₐ summing to the identity. Its average error is 1−M⁻¹∑ₐ Re Tr(DₐΦₙ(Pₐ)). A rate R is defined to be achievable if a sequence of codes has error tending to zero and, for every ε>0, eventually log₂(Mₙ)/n≥R−ε; capacity is the supremum of achievable rates. Writing h(x)=−x ln x−(1−x)ln(1−x), define g(u)=h((1+√(1−4u))/2), v(γ,ν,p)=γν(1−ν)+γ(1−γ)(p−ν)², and objective(γ,ν,p)=h((1−γ)p+γν)−g(v(γ,ν,p)). Maximizes asserts that p lies in [0,1] and attains the largest objective on that interval. Finally, phase signals have amplitudes (√(1−p), ±√p), with the sign selected independently at each qubit; their tensor-product outer products define phase states, and phaseValue is the Holevo expression for all 2ⁿ such outputs with equal weights. No claim of optimality or equality between capacity and these expressions is established in this block.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/AmplitudeDamping.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/AmplitudeDamping.lean; bytes 16..4308
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

universe u

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix Filter

namespace GAD

abbrev Basis (n : ℕ) := Fin n → Fin 2
abbrev QMatrix (n : ℕ) := Matrix (Basis n) (Basis n) ℂ

/-- The spectral definition of -Tr(P log P), with 0 log 0 = 0. -/
def entropy {ι : Type u} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (cfc Real.negMulLog P)).re

def IsState {ι : Type u} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : Prop :=
  P.PosSemidef ∧ Matrix.trace P = 1


def kraus (γ ν : ℝ) (r : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if r = 0 then
    !![(Real.sqrt (1 - ν) : ℂ), 0;
       0, (Real.sqrt (1 - ν) * Real.sqrt (1 - γ) : ℂ)]
  else if r = 1 then
    !![0, (Real.sqrt (γ * (1 - ν)) : ℂ); 0, 0]
  else if r = 2 then
    !![(Real.sqrt ν * Real.sqrt (1 - γ) : ℂ), 0; 0, (Real.sqrt ν : ℂ)]
  else
    !![0, 0; (Real.sqrt (γ * ν) : ℂ), 0]

/-- Tensor products of the single-site Kraus operators, with the full Kraus index. -/
def tensorKraus (γ ν : ℝ) (n : ℕ) (r : Fin n → Fin 4) : QMatrix n :=
  fun i j ↦ ∏ k, kraus γ ν (r k) (i k) (j k)

/-- The memoryless n-fold generalized amplitude-damping channel. -/
def channel (γ ν : ℝ) (n : ℕ) (P : QMatrix n) : QMatrix n :=
  ∑ r : Fin n → Fin 4,
    tensorKraus γ ν n r * P * (tensorKraus γ ν n r).conjTranspose

/-- All finite ensembles, without any product or purity restriction. -/
structure Ensemble (n : ℕ) where
  size : ℕ
  weight : Fin size → ℝ
  weight_nonneg : ∀ a, 0 ≤ weight a
  weight_sum : ∑ a, weight a = 1
  signal : Fin size → QMatrix n
  signal_state : ∀ a, IsState (signal a)

def ensembleValue (γ ν : ℝ) {n : ℕ} (E : Ensemble n) : ℝ :=
  (entropy (∑ a, (E.weight a : ℂ) • channel γ ν n (E.signal a)) -
    ∑ a, E.weight a * entropy (channel γ ν n (E.signal a))) / Real.log 2


def holevo (γ ν : ℝ) (n : ℕ) : ℝ :=
  sSup (Set.range (ensembleValue γ ν : Ensemble n → ℝ))

/-- An unrestricted n-use quantum code with one collective output POVM. -/
structure Code (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encoding : Fin messages → QMatrix n
  encoding_state : ∀ a, IsState (encoding a)
  decoding : Fin messages → QMatrix n
  decoding_pos : ∀ a, (decoding a).PosSemidef
  decoding_sum : ∑ a, decoding a = 1

def averageError (γ ν : ℝ) {n : ℕ} (C : Code n) : ℝ :=
  1 - (∑ a, (Matrix.trace (C.decoding a * channel γ ν n (C.encoding a))).re) /
    (C.messages : ℝ)

/-- The liminf rate condition written as its eventual lower-bound characterization.
There is no preshared entanglement, feedback, or restriction on encodings/decoding. -/
def Achievable (γ ν R : ℝ) : Prop :=
  ∃ C : (n : ℕ) → Code n,
    Tendsto (fun n ↦ averageError γ ν (C n)) atTop (nhds 0) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      R - ε ≤ Real.log ((C n).messages : ℝ) / Real.log 2 / (n : ℝ)

/-- Operational unassisted classical capacity, not a definition by regularization. -/
def capacity (γ ν : ℝ) : ℝ := sSup {R : ℝ | Achievable γ ν R}

def g (u : ℝ) : ℝ := Real.binEntropy ((1 + Real.sqrt (1 - 4 * u)) / 2)

def v (γ ν p : ℝ) : ℝ := γ * ν * (1 - ν) + γ * (1 - γ) * (p - ν) ^ 2

def objective (γ ν p : ℝ) : ℝ :=
  Real.binEntropy ((1 - γ) * p + γ * ν) - g (v γ ν p)

def Maximizes (γ ν p : ℝ) : Prop :=
  p ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ q ∈ Set.Icc (0 : ℝ) 1, objective γ ν q ≤ objective γ ν p


def phaseSignal (p : ℝ) (s b : Fin 2) : ℂ :=
  if b = 0 then (Real.sqrt (1 - p) : ℂ)
  else if s = 0 then (Real.sqrt p : ℂ) else -(Real.sqrt p : ℂ)

def phaseProduct (p : ℝ) {n : ℕ} (s : Basis n) (i : Basis n) : ℂ :=
  ∏ k, phaseSignal p (s k) (i k)

def phaseState (p : ℝ) {n : ℕ} (s : Basis n) : QMatrix n :=
  fun i j ↦ phaseProduct p s i * star (phaseProduct p s j)

/-- Holevo value of the explicit 2^n equiprobable product signals. -/
def phaseValue (γ ν p : ℝ) (n : ℕ) : ℝ :=
  (entropy (∑ s : Basis n, (((2 : ℝ) ^ n)⁻¹ : ℂ) • channel γ ν n (phaseState p s)) -
    ∑ s : Basis n, ((2 : ℝ) ^ n)⁻¹ * entropy (channel γ ν n (phaseState p s))) /
    Real.log 2



end GAD
end
end OAI


