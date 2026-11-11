-- Prove2me | Definitions.Def_DistributedMWC440_UpperBound_Operations
-- name    : DistributedMWC440_UpperBound_Operations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T15:25:00.734674+00:00
-- url     : https://prove2.me/theorems/a0b3ca3a-22f9-438f-9c93-0ce0a6118903
-- title:
--   Scheduling, hop SSSP, sampling, and branch resource interfaces
-- statement:
--   The deterministic hop-SSSP interface decodes actual local rational labels and parent ports, charges both-direction edge use, and asks for approximation, a finite-label rooted tree, height, congestion and rounds as conclusions. Scheduling couples a local scheduler to independent isolated protocol executions at their first completion times, for collections of at most n^a algorithms with the exponent a fixed in advance. Skeletons are Bernoulli(alpha/n); good samples require two cycle skeletons, short segments, and sample size between alpha/2 and 2 alpha. The long-run probability is the full Bernoulli mixture of conditional continuous shifts and independent parities. The short-hop weight perturbation and integer scaling are explicit. Short and long task predicates keep all program, confidence, width and time quantifiers before the unknown network.
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, §§1, 3–7, printed pp. 1–43 / PDF pp. 3–45.

import Definitions.Def_DistributedMWC440_UpperBound_CONGEST
import Definitions.Def_DistributedMWC440_UpperBound_Clustering

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

/-- Deterministic algorithms consume no random bits. -/
def Deterministic (A : Protocol) : Prop := ∀ z, A.bitCount z = 0

def sourceInput {n : ℕ} (x v : Fin n) : List ℕ := if v = x then [1] else [0]

def ssspState {n q b} (I : Network n q b) (A : Protocol) (x : Fin n) (t : ℕ) :=
  stateAtInput I A (sourceInput x) (fun _ => false) t

def decodedLabel (A : Protocol) (s : ℕ) : ℝ≥0∞ :=
  ((A.distance s).map (fun z => ENNReal.ofReal (z : ℝ))).getD ⊤

def decodedParent {n q b} (I : Network n q b) (A : Protocol)
    (state : Fin n → ℕ) (v : Fin n) : Fin n :=
  match A.parentPort (state v) with
  | none => v
  | some p => if h : p < degree I v then (I.ports v ⟨p,h⟩).val else v

def widthOfStates {n q b} (I : Network n q b) (A : Protocol) (B : ℕ)
    (state : ℕ → Fin n → ℕ) (t : ℕ) : Prop :=
  ∀ r < t, ∀ v, ∀ p < degree I v, ∀ m, sent A (state r v) p = some m →
    m < (max 2 n)^B ∧ A.halt (state r v) = false

/-- One unit of undirected congestion is charged for a round in which either endpoint sends. -/
def edgeUse {n q b} (I : Network n q b) (A : Protocol)
    (state : ℕ → Fin n → ℕ) (u v : Fin n) (r : ℕ) : Prop :=
  ∃ p : Fin (degree I u), (I.ports u p).val = v ∧ sent A (state r u) p.val ≠ none

def congestionOn {n q b} (I : Network n q b) (A : Protocol)
    (state : ℕ → Fin n → ℕ) (t : ℕ) (u v : Fin n) : ℕ := by
  classical
  exact ((Finset.range t).filter fun r => edgeUse I A state u v r ∨ edgeUse I A state v u r).card

/-- No assumption supplies a fast or correct SSSP algorithm: this predicate is the desired
existential operational algorithm theorem, including its parent tree, height and messages. -/
def HopSSSPAvailable (q b : ℕ) : Prop :=
  ∃ (B n₀ : ℕ) (C : ℝ), 0 < C ∧
  ∀ h : ℕ, 1 ≤ h → ∀ ε : ℝ, 0 < ε → ε < 1 →
  ∃ A : Protocol, Deterministic A ∧
    ∀ n ≥ max 2 n₀, ∀ I : Network n q b, ∀ x : Fin n,
      (∀ t, widthOfStates I A B (ssspState I A x) t) ∧
      ∃ t : ℕ, (t : ℝ) ≤ C * (h / ε) * Real.log n ∧
        (∀ v, A.halt (ssspState I A x t v) = true) ∧
        (∀ u v, (congestionOn I A (ssspState I A x) t u v : ℝ) ≤ C * Real.log n) ∧
        ∃ T : HopTree I.W x,
          (∀ v, T.label v = decodedLabel A (ssspState I A x t v)) ∧
          T.parent = decodedParent I A (ssspState I A x t) ∧
          HopApprox I.W x h ε T.label ∧ T.heightBound (C*(h/ε)*Real.log n)

def StopsAt {n q b} (I : Network n q b) (A : Protocol) (ω : Tapes n) (t : ℕ) : Prop :=
  Halted I A ω t ∧ ∀ r < t, ¬Halted I A ω r

def collectionCongestion {n q b r} (I : Network n q b) (A : Fin r → Protocol)
    (ω : Fin r → Tapes n) (T : Fin r → ℕ) : ℕ :=
  sSup {c | ∃ u v : Fin n,
    c = ∑ i, congestionOn I (A i) (stateAt I (A i) (ω i)) (T i) u v}

def collectionDilation {r : ℕ} (T : Fin r → ℕ) : ℕ := sSup (Set.range T)

/-- Execution is observable final-state equivalence with the isolated local programs.
The scheduler is itself a local computable CONGEST protocol and receives no future traffic.
The number of algorithms is at most a fixed polynomial `n ^ a` in the network size: with
superpolynomially many algorithms the `O(log n)`-bit links cannot even convey which of them
sent a message within polylogarithmic overhead. -/
def SchedulingAvailable (q b : ℕ) : Prop :=
  ∀ (B₀ a : ℕ) (confidence : ℝ), 0 < confidence →
  ∃ (B p n₀ : ℕ) (C : ℝ), 0 < C ∧
  ∀ (r : ℕ) (A : Fin r → Protocol), ∃ scheduler : Protocol,
    ∀ n ≥ max 2 n₀, r ≤ n ^ a → ∀ I : Network n q b,
      (∀ i ω t, WidthBound I (A i) B₀ ω t) →
      (∀ i ω, ∃ t, Halted I (A i) ω t) →
      (∀ ω t, WidthBound I scheduler B ω t) ∧
      ∃ μ : Measure (Tapes n × (Fin r → Tapes n)),
        Measure.map Prod.fst μ = tapeLaw n ∧
        Measure.map Prod.snd μ = Measure.pi (fun _ : Fin r => tapeLaw n) ∧
        MeasurableSet {z : Tapes n × (Fin r → Tapes n) |
          ∃ (T : Fin r → ℕ) (t : ℕ),
            (∀ i, StopsAt I (A i) (z.2 i) (T i)) ∧
            (t : ℝ) ≤ C*(Real.log n)^p *
              (collectionCongestion I A z.2 T + collectionDilation T : ℕ) ∧
            Halted I scheduler z.1 t ∧
            ∀ v, Encodable.decode (α := List ℕ)
                ((scheduler.value (stateAt I scheduler z.1 t v)).getD 0) =
              some (List.ofFn fun i : Fin r => stateAt I (A i) (z.2 i) (T i) v)} ∧
        ENNReal.ofReal (1 - (n : ℝ)^(-confidence)) ≤ μ
          {z | ∃ (T : Fin r → ℕ) (t : ℕ),
            (∀ i, StopsAt I (A i) (z.2 i) (T i)) ∧
            (t : ℝ) ≤ C*(Real.log n)^p *
              (collectionCongestion I A z.2 T + collectionDilation T : ℕ) ∧
            Halted I scheduler z.1 t ∧
            ∀ v, Encodable.decode (α := List ℕ)
                ((scheduler.value (stateAt I scheduler z.1 t v)).getD 0) =
              some (List.ofFn fun i : Fin r => stateAt I (A i) (z.2 i) (T i) v)}

variable {V : Type} [Fintype V] [DecidableEq V]

def bernoulli (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1-p) • Measure.dirac false

def samplingLaw (α : ℝ) : Measure (V → Bool) :=
  Measure.pi (fun _ => bernoulli (α / Fintype.card V))

def sampled (σ : V → Bool) : Finset V := Finset.univ.filter fun v => σ v

def cycleSkeleton {W : WGraph V} (C : Cycle W) (S : Finset V) : Finset V :=
  S.filter fun v => v ∈ C.walk.support

def GoodSample {W : WGraph V} (C : Cycle W) (S : Finset V) (α c : ℝ) : Prop :=
  2 ≤ (cycleSkeleton C S).card ∧
  SegmentBound C (cycleSkeleton C S) (c * (Fintype.card V / α) * Real.log (Fintype.card V)) ∧
  α / 2 ≤ S.card ∧ (S.card : ℝ) ≤ 2*α

/-- The joint experiment samples skeletons first, then real exponential shifts at the resulting
rate, then independent parity bits. Samples of fewer than two centers produce no candidate. -/
def LongRunProbability (W : WGraph V) (k ε α : ℝ) (d : Finset V → ℝ) (L : ℕ)
    (run : ∀ S, 2 ≤ S.card → (δ : Shifts S) → LDDTree W S k (d S) ε δ)
    (patch : ∀ S (hS : 2 ≤ S.card) (δ : Shifts S) (χ : Parities V),
      PatchOutputs (run S hS δ) χ L) (bound : ℝ) : ℝ≥0∞ := by
  classical
  exact ∑ σ : V → Bool,
    samplingLaw α {σ} *
    if hS : 2 ≤ (sampled σ).card then
      ((shiftLaw (sampled σ) (rate (sampled σ) k (d (sampled σ)))).prod parityLaw)
        {z | ExtendedSuccess (patch (sampled σ) hS z.1 z.2) bound}
    else 0

/-- Section 7.2's actual perturbation, before finite precision implementation. -/
def perturbed (W : WGraph V) (d ε : ℝ) (h : ℕ) (hτ : 0 ≤ ε*(2*d)/h) : WGraph V where
  graph := W.graph
  length u v := W.length u v + ε*(2*d)/h
  symmetric u v := by rw [W.symmetric u v]
  nonnegative u v huv := add_nonneg (W.nonnegative u v huv) hτ

/-- Section 5.2's integer scaling; no replacement of the real exponential law. -/
def scaledLength (ℓ : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ)^3 * ℓ⌉₊

/-- Short-hop promise applies only to correctness/time; the protocol receives no optimum cycle. -/
def ShortTradeoff (q b : ℕ) : Prop :=
  ∀ confidence : ℝ, 0 < confidence →
  ∃ (B p n₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ (k : ℝ), 1 ≤ k → ∀ h : ℕ, 1 ≤ h →
    ∃ A : Protocol, ∀ n ≥ max 2 n₀, ∀ I : Network n q b,
      (∀ ω t, WidthBound I A B ω t) ∧
      (shortPromise h I →
       let budget := C*(Real.log n)^p * shortCost k h n (diameter I)
       MeasurableSet (MWCEvent I A B (k+1) budget) ∧
       ENNReal.ofReal (1-(n : ℝ)^(-confidence)) ≤ tapeLaw n (MWCEvent I A B (k+1) budget))

/-- The exponent in alpha >= n^a and the hop threshold coefficient are fixed before inputs.
No good-sample event or SSSP guarantee is an input hypothesis. -/
def LongTradeoff (q b : ℕ) : Prop :=
  ∀ (a cHop confidence : ℝ), 0 < a → 0 < cHop → 0 < confidence →
  ∃ (B p n₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ k : ℝ, 1 ≤ k →
    ∀ α : ℝ, 0 < α → ∃ A : Protocol, ∀ n ≥ max 2 n₀,
    (n : ℝ)^a ≤ α → α ≤ n → ∀ I : Network n q b,
      (∀ ω t, WidthBound I A B ω t) ∧
      (longPromise (fun _ => α) cHop I →
       let budget := C*(Real.log n)^p * (α^(1+1/k) + n/α + diameter I)
       MeasurableSet (MWCEvent I A B (k+1) budget) ∧
       ENNReal.ofReal (1-(n : ℝ)^(-confidence)) ≤ tapeLaw n (MWCEvent I A B (k+1) budget))

end DistributedMWC440.UpperBound


