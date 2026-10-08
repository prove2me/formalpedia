-- Prove2me | Definitions.Def_MatroidSecretary
-- name    : MatroidSecretary
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:18.860189+00:00
-- url     : https://prove2.me/theorems/e53d360d-b50f-4ad2-b63e-041d51d4a5cf
-- statement:
--   This block formalizes three defined propositions about online selection in a matroid on Fin n with nonnegative weights, and does not prove any of them. Weights are vectors Fin n → ℝ, arrival orders are permutations of Fin n, and the history at position k is the list of (element, weight) pairs seen through position k. An OnlineRule with a finite seed space Fin bits → Bool has a measurable decision function that, at each position, sees the seed, a weight vector s, and the history, and answers accept or reject. Accepted elements through time t are those arriving before t that were accepted, the reward is their total true weight, optimum M v is the maximum weight of an independent set, and Feasible means the accepted set is independent for every seed, nonnegative s and v, order and time. OneSampleChallenge states that for every matroid on Fin n with ground set all of Fin n there are a seed length, a probability law on seeds and a feasible rule such that, for any random nonnegative weights S (one sample) and V (the realized weights) with independent coordinates across the paired family, S and V identically distributed per element, seed independent of (S,V) with the given law, integrable optimum, and any measurable arrival order, the reward is integrable and its expectation is at least 2^(-310) times the expected optimum. HiddenRule adds a seed-dependent mask of elements, observed weights are the true weights on the mask and zero elsewhere, masked elements are removed from the accepted set, and the worst reward is the minimum over seeds. HiddenVectorChallenge asserts, for every such matroid, a seed law and hidden rule that is always independent for nonnegative weights and, for each fixed nonnegative weight vector, has seed-expected worst-case reward at least 2^(-293) times the optimum. SecretaryRule has a random prefix length and a measurable decision rule, rejecting during the prefix. SamePrefix says two orders agree on the first K positions. SecretaryChallenge asserts, for every such matroid, a finite seed space Fin q with a probability law and a feasible secretary rule such that for every fixed nonnegative weight vector, whenever the seed is independent of a uniformly random order σ and the actual arrival order π agrees almost surely with σ on the sampled prefix, the reward is integrable with expectation at least 2^(-293) times optimum.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatroidSecretary.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatroidSecretary.lean; bytes 16..8454
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
# Matroid selection against an almighty adversary

The three guarantees concern one independent sample per label, a hidden fixed
weight vector, and a uniformly sampled observation prefix. The rule and its
finite seed law are fixed before the input weights or value distributions.
-/

open scoped BigOperators

section

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

end

section

open MeasureTheory
open scoped BigOperators

namespace MatroidProphet

instance arrivalOrderMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (ArrivalOrder n) := ⟨fun _ => trivial⟩

structure HiddenRule (n bits : ℕ) where
  mask : Seed bits → Finset (Fin n)
  core : OnlineRule n bits

noncomputable def observed {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (w : Weights n) : Weights n := by
  classical
  exact fun e => if e ∈ A.mask r then w e else 0

noncomputable def hiddenAcceptedThrough {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) (t : ℕ) : Finset (Fin n) :=
  acceptedThrough A.core r (observed A r w) w π t \ A.mask r

noncomputable def hiddenReward {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) : ℝ :=
  ∑ e ∈ hiddenAcceptedThrough A r w π n, w e

noncomputable def hiddenWorstReward {n bits : ℕ} (A : HiddenRule n bits)
    (w : Weights n) (r : Seed bits) : ℝ := by
  classical
  exact Finset.univ.inf' Finset.univ_nonempty (hiddenReward A r w)

end MatroidProphet

end

section

open MeasureTheory ProbabilityTheory

namespace MatroidProphet

def HiddenVectorChallenge : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
    ∃ (bits : ℕ) (ν : Measure (Seed bits)), IsProbabilityMeasure ν ∧
    ∃ (A : HiddenRule n bits),
      (∀ (w : Weights n), (∀ e, 0 ≤ w e) →
        ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
          M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n))) ∧
      ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
        ((2 : ℝ) ^ 293)⁻¹ * optimum M w ≤
          ∫ r, hiddenWorstReward A w r ∂ν

end MatroidProphet

end

section

open MeasureTheory

namespace MatroidProphet

structure SecretaryRule (n : ℕ) (Q : Type*) [MeasurableSpace Q] where
  prefixLength : Q → Fin (n + 1)
  measurable_prefixLength : Measurable prefixLength
  decide : (k : Fin n) → Q → History n k → Bool
  measurable_decide : ∀ k, Measurable
    (fun x : Q × History n k => decide k x.1 x.2)

def SamePrefix {n : ℕ} (K : ℕ) (σ π : ArrivalOrder n) : Prop :=
  ∀ k : Fin n, k.val < K → σ k = π k

def secretaryDecisionAt {n : ℕ} {Q : Type*} [MeasurableSpace Q]
    (A : SecretaryRule n Q) (q : Q) (w : Weights n) (π : ArrivalOrder n)
    (k : Fin n) : Bool :=
  if k.val < (A.prefixLength q).val then false else A.decide k q (history w π k)

noncomputable def secretaryAcceptedThrough {n : ℕ} {Q : Type*} [MeasurableSpace Q]
    (A : SecretaryRule n Q) (q : Q) (w : Weights n) (π : ArrivalOrder n)
    (t : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun e =>
    (π.symm e).val < t ∧ secretaryDecisionAt A q w π (π.symm e) = true

noncomputable def secretaryReward {n : ℕ} {Q : Type*} [MeasurableSpace Q]
    (A : SecretaryRule n Q) (q : Q) (w : Weights n) (π : ArrivalOrder n) : ℝ :=
  ∑ e ∈ secretaryAcceptedThrough A q w π n, w e

def SecretaryFeasible {n : ℕ} {Q : Type*} [MeasurableSpace Q]
    (M : Matroid (Fin n)) (A : SecretaryRule n Q) : Prop :=
  ∀ (q : Q) (w : Weights n), (∀ e, 0 ≤ w e) →
    ∀ (π : ArrivalOrder n) (t : ℕ),
      M.Indep (secretaryAcceptedThrough A q w π t : Set (Fin n))

end MatroidProphet

end

section

namespace MatroidProphet.Secretary

open MeasureTheory

noncomputable def uniformArrivalLaw (n : ℕ) : Measure (ArrivalOrder n) :=
  (PMF.uniformOfFintype (ArrivalOrder n)).toMeasure

end MatroidProphet.Secretary

end

section

open MeasureTheory ProbabilityTheory

namespace MatroidProphet

def SecretaryChallenge.{u} : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
    ∃ (q : ℕ) (ν : Measure (Fin q)), IsProbabilityMeasure ν ∧
    ∃ (A : SecretaryRule n (Fin q)), SecretaryFeasible M A ∧
      ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Q : Ω → Fin q) (σ π : Ω → ArrivalOrder n),
        Measurable Q → Measurable σ → Measurable π →
        Measure.map Q μ = ν →
        Measure.map σ μ = Secretary.uniformArrivalLaw n →
        IndepFun Q σ μ →
        (∀ᵐ ω ∂μ, SamePrefix (A.prefixLength (Q ω)).val (σ ω) (π ω)) →
        Integrable (fun ω => secretaryReward A (Q ω) w (π ω)) μ ∧
          ((2 : ℝ) ^ 293)⁻¹ * optimum M w ≤
            ∫ ω, secretaryReward A (Q ω) w (π ω) ∂μ

end MatroidProphet

end

namespace MatroidProphet.Assigned



end MatroidProphet.Assigned
end OAI


