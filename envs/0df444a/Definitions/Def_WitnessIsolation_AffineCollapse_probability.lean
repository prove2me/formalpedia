-- Prove2me | Definitions.Def_WitnessIsolation_AffineCollapse_probability
-- name    : WitnessIsolation_AffineCollapse_probability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:40.060094+00:00
-- url     : https://prove2.me/theorems/9b4deb9b-b58f-4e40-90a6-9f38bf866ebc
-- title:
--   Real finite laws and arbitrary-private-law experiments
-- statement:
--   A law on a finite set assigns arbitrary nonnegative real masses summing to one. Its expectation and event probability are finite weighted sums. Two laws μ,ν on binary strings are indistinguishable at budget S and parameter ε if every circuit C with at most S gates satisfies
--
--   $$|\Pr_\mu[C=1]-\Pr_\nu[C=1]|\le\epsilon.$$
--
--   A unique source is a well-formed padded description with the specified declared dimension and exactly one solution; a null source has none. The witness relation identifies the satisfying assignment without supplying it to any circuit. The cost of evaluation at a fixed assignment is the minimum gate count of circuits evaluating that relation on descriptions.
--
--   The hybrid experiment first fixes private data π, draws independent sources, and averages its Boolean output over a uniform tape. The inactive source positions receive ν in the mixed experiment and μ in the reference experiment; other positions receive μ in both. The outer private-data integral is left to the theorem so that its law may be arbitrary. The inactive maximum is the supremum of the integer cardinalities, a bounded subset of {0,…,m}.
--
--   These are probability and resource definitions; no indistinguishability, atom bound, hybrid bound, or decider-existence fact is assumed. They permit real, nonsamplable source laws and private laws without finite support.
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), §3, printed pp. 7–8, PDF pp. 8–9, Eq. (3.1) and Lemmas 3.1–3.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/346.pdf; PDF SHA256 969057d4c1837a5ebf1d45c70a14c1d66f0d76610c6233f151e2402e7611f42e

import Definitions.Def_WitnessIsolation_AffineCollapse_model

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse

/-- Arbitrary real masses, with no computability or rationality assumption. -/
structure Law (α : Type) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

def Law.expect {α : Type} [Fintype α] (μ : Law α) (f : α → ℝ) : ℝ :=
  ∑ x, μ.mass x * f x

def Law.prob {α : Type} [Fintype α] (μ : Law α) (E : α → Prop) : ℝ := by
  classical
  exact μ.expect (fun x => if E x then 1 else 0)

def Law.Supported {α : Type} [Fintype α] (μ : Law α) (Y : Set α) : Prop :=
  ∀ x, x ∉ Y → μ.mass x = 0

def Indistinguishable {ℓ : ℕ} (μ ν : Law (Bits ℓ)) (S : ℕ) (ε : ℝ) : Prop :=
  ∀ C : Circuit ℓ 1, C.size ≤ S → |μ.prob C.accepts - ν.prob C.accepts| ≤ ε

def Separates {ℓ : ℕ} (C : Circuit ℓ 1) (Y N : Set (Bits ℓ)) : Prop :=
  (∀ y ∈ Y, C.accepts y) ∧ (∀ z ∈ N, ¬C.accepts z)

/-- A source's witness is unique; sources use the same padded cap and declared dimension. -/
def IsUniqueSource (ℓ v : ℕ) (x : Bits (paddedWidth ℓ)) : Prop :=
  ∃ d, decodedPadded ℓ x = some d ∧ d.inputs = v ∧ d.sol.card = 1

def IsNullSource (ℓ v : ℕ) (x : Bits (paddedWidth ℓ)) : Prop :=
  ∃ d, decodedPadded ℓ x = some d ∧ d.inputs = v ∧ d.sol.card = 0

def WitnessRelation (ℓ v : ℕ) (E : Bits (paddedWidth ℓ)) (x : Bits v) : Prop :=
  ∃ d, decodedPadded ℓ E = some d ∧ d.inputs = v ∧
    d.eval (word (List.ofFn x) d.inputs) = true

/-- Real cost minimum for fixed-point evaluation, infinite only if no finite implementation exists. -/
def evaluationCost (ℓ v : ℕ) (x : Bits v) : ℕ∞ :=
  ⨅ C : {C : Circuit (paddedWidth ℓ) 1 //
      ∀ E, C.accepts E ↔ WitnessRelation ℓ v E x}, (C.val.size : ℕ∞)

/-- Product mass, so repeated sources are independent even when their witnesses collide. -/
def sampleExpectation {α : Type} [Fintype α] {m : ℕ}
    (μ : Fin m → Law α) (f : (Fin m → α) → ℝ) : ℝ :=
  ∑ E, (∏ i, (μ i).mass (E i)) * f E

/-- Conditional finite-source expectation; the outer integral admits arbitrary private laws. -/
def experiment {Ω : Type} {m ℓ r : ℕ} (μ ν : Law (Bits ℓ))
    (I : Ω → Finset (Fin m)) (f : Ω → Bits r → (Fin m → Bits ℓ) → Bool)
    (π : Ω) (mixed : Bool) : ℝ := by
  classical
  exact (∑ ρ : Bits r,
    sampleExpectation (fun i => if mixed = true ∧ i ∈ I π then ν else μ)
      (fun E => if f π ρ E then 1 else 0)) / (2:ℝ)^r

/-- Maximum is over the private-data carrier, not merely its support; empty carrier gives zero. -/
def inactiveMaximum {Ω : Type} {m : ℕ} (I : Ω → Finset (Fin m)) : ℕ :=
  sSup (Set.range (fun π => (I π).card))

end WitnessIsolation.AffineCollapse


