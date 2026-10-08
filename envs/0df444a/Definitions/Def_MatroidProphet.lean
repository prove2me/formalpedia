-- Prove2me | Definitions.Def_MatroidProphet
-- name    : MatroidProphet
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:18.791456+00:00
-- url     : https://prove2.me/theorems/6039aadc-1978-477d-b3d7-d8675541ff6f
-- statement:
--   This block formalizes one-sample prophet-type selection on a known matroid over the ground set Fin n, and then defines a challenge proposition about it. Weights, samples and values are functions Fin n → ℝ, a seed is a vector of bits Boolean values, and an arrival order is a permutation of Fin n. An OnlineRule with n elements and bits seed bits is a decision function that, at step k, sees the seed, the whole initial sample vector, and the history of the first k+1 arrivals as (label, value) pairs, and returns accept or reject; it is required to be jointly measurable in these inputs. Given sample vector s, values v, seed r and order π, the rule's decision at step k uses the history of v along π, and acceptedThrough t is the set of elements arriving before position t that were accepted, so decisions are irrevocable; accepted is the set after all n steps, and reward is the sum of v over it. The optimum of a matroid M for values v is the maximum of the total value of an independent set (zero for dependent candidates, so the empty set counts). Feasible M A says that for every seed, every nonnegative sample vector and value vector, every order and every time t, the set accepted through time t is independent in M, so every prefix is feasible. pairedCoordinates S V indexes the 2n coordinates by (element, Bool), returning the sample coordinate when the flag is true and the value coordinate otherwise. OneSampleChallenge is a defined proposition, not a proved theorem. It says that for every n and every matroid M on Fin n with ground set all of Fin n, there exist a bit length, a probability measure ν on seeds, and a feasible online rule such that the following holds for every probability space carrying measurable nonnegative (almost surely) random sample and value vectors S and V and a seed R. The 2n coordinates of the pairs must be mutually independent, S e and V e must have the same distribution for each e, the pair (S,V) must be independent of R, R must have law ν, and the optimum of M at V must be integrable. Then for every measurable random arrival order π, which may depend on samples, values and seed, the reward is integrable and its expectation is at least 2^(-310) times the expected optimum. The rule and seed law depend only on M, not on the distributions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatroidProphet.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatroidProphet.lean; bytes 16..3912
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
# One-sample matroid selection

The rule and its finite seed law depend only on the known labeled matroid.
A decision sees the initial sample vector, the entire seed, and the arriving
label/value prefix. Every prefix is feasible, and decisions are irrevocable.
The arrival permutation may depend on all samples, values, and seed bits.
Only the actual offline optimum is required to be integrable.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MatroidProphet

abbrev Weights (n : ℕ) := Fin n → ℝ
abbrev Seed (bits : ℕ) := Fin bits → Bool
abbrev ArrivalOrder (n : ℕ) := Equiv.Perm (Fin n)
instance arrivalOrderMeasurableSpace (n : ℕ) : MeasurableSpace (ArrivalOrder n) := ⊤

abbrev History (n : ℕ) (k : Fin n) := Fin (k.val + 1) → Fin n × ℝ

structure OnlineRule (n bits : ℕ) where
  decide : (k : Fin n) → Seed bits → Weights n → History n k → Bool
  measurable_decide : ∀ k, Measurable
    (fun x : Seed bits × (Weights n × History n k) => decide k x.1 x.2.1 x.2.2)

def prefixIndex {n : ℕ} (k : Fin n) (j : Fin (k.val + 1)) : Fin n :=
  ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩

def history {n : ℕ} (v : Weights n) (π : ArrivalOrder n) (k : Fin n) : History n k :=
  fun j => let e := π (prefixIndex k j); (e, v e)

def decisionAt {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (k : Fin n) : Bool :=
  A.decide k r s (history v π k)

noncomputable def acceptedThrough {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun e =>
    (π.symm e).val < t ∧ decisionAt A r s v π (π.symm e) = true

noncomputable def accepted {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) : Finset (Fin n) :=
  acceptedThrough A r s v π n

noncomputable def reward {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) : ℝ :=
  ∑ e ∈ accepted A r s v π, v e

noncomputable def optimum {n : ℕ} (M : Matroid (Fin n)) (v : Weights n) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun I : Finset (Fin n) => if M.Indep (I : Set (Fin n)) then ∑ e ∈ I, v e else 0)

def Feasible {n bits : ℕ} (M : Matroid (Fin n)) (A : OnlineRule n bits) : Prop :=
  ∀ (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ),
    (∀ e, 0 ≤ s e) → (∀ e, 0 ≤ v e) →
    M.Indep (acceptedThrough A r s v π t : Set (Fin n))

def pairedCoordinates.{u} {n : ℕ} {Ω : Type u} (S V : Ω → Weights n)
    (i : Fin n × Bool) : Ω → ℝ :=
  if i.2 then fun ω => S ω i.1 else fun ω => V ω i.1

def OneSampleChallenge.{u} : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
    ∃ (bits : ℕ) (ν : Measure (Seed bits)), IsProbabilityMeasure ν ∧
    ∃ (A : OnlineRule n bits), Feasible M A ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (S V : Ω → Weights n) (R : Ω → Seed bits),
        Measurable S → Measurable V → Measurable R →
        (∀ᵐ ω ∂μ, ∀ e, 0 ≤ S ω e) →
        (∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e) →
        iIndepFun (pairedCoordinates S V) μ →
        (∀ e, Measure.map (fun ω => S ω e) μ = Measure.map (fun ω => V ω e) μ) →
        IndepFun (fun ω => (S ω, V ω)) R μ →
        Measure.map R μ = ν →
        Integrable (fun ω => optimum M (V ω)) μ →
        ∀ (π : Ω → ArrivalOrder n), Measurable π →
          Integrable (fun ω => reward A (R ω) (S ω) (V ω) (π ω)) μ ∧
          ((2 : ℝ) ^ 310)⁻¹ * (∫ ω, optimum M (V ω) ∂μ) ≤
            ∫ ω, reward A (R ω) (S ω) (V ω) (π ω) ∂μ



end MatroidProphet
end OAI


