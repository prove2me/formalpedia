-- Prove2me | Definitions.Def_GaussianFiniteEntropy
-- name    : GaussianFiniteEntropy
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:12.35677+00:00
-- url     : https://prove2.me/theorems/cfe1a81c-b51f-4f11-91d4-885e327fd167
-- statement:
--   The file sets up a repeated-localization experiment on the n-dimensional cube [-1/(2√n),1/(2√n))^n, with uniform prior, and a dyadic cell structure, then defines a finite-entropy statement about an adaptive refinement procedure. A Cell n is a pair (J,q) with q assigning each of n coordinates an index in {0,…,2^J−1}; its cellSet is the half-open dyadic subcube with side 1/(√n·2^J) anchored at the cube's lower corner, and the root cell (J=0) is the whole cube. Background definitions include a chart z ↦ (z, √(1−|z|²)) onto the upper unit sphere in n+1 dimensions, a Gaussian block of ⌊n/16⌋ rows of i.i.d. standard Gaussian vectors in ℝ^(n+1), exact labels given by row inner products with chart(z), block rules that choose among N outcomes with measurable probabilities, histories of length t, the resulting joint law of (z, history), valid disclosures (finite-range measurable nested cell choices containing z inside the cube), mutual information as KL divergence from the product of marginals, and a MainStatement proposition asserting a bound of order (n+1)t on information and t on expected final level under a smallness condition on N. The finite-entropy part works relative to a probability measure P. For cells Q and a strict descendant R at depth h=R.1−Q.1, R is heavy if P(R) exceeds the threshold 2^(−nh/2), and first heavy if no other heavy cell of Q is a descendant of R besides R itself. The residual is Q minus all first-heavy cells. An attempt reveals a letter, either the first-heavy cell containing z or none if z lies in the residual; a state records the current cell, the conditioning event and a stopped flag, which is set when a none letter occurs on an event of conditional probability at least 1/2. Running the procedure yields logs of letters, with termination, number of attempts, terminal log, terminal cell, terminal law (P conditioned on the log) and depth (terminal level minus Q's level). A measure is Regular on Q if it gives Q mass one and every strict descendant R has mass at most 2·threshold. FiniteEntropyStatement is a defined proposition, not an established theorem: there is n₀ such that for all n≥n₀, every cell Q, and every probability measure P absolutely continuous with respect to the uniform measure on Q with finite KL divergence, the procedure terminates P-almost surely, the terminal log is measurable, each positive-probability log has a terminal cell descending from Q with regular terminal law, depth and attempts are integrable, expected attempts are at most 2(1+expected depth), and the expected terminal KL divergence plus (log 2/4)·n·expected depth is at most KL(P‖uniform on Q) + 2/e.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GaussianFiniteEntropy.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GaussianFiniteEntropy.lean; bytes 16..9052
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

abbrev Coordinate (n : ℕ) := Fin n → ℝ
abbrev GaussianBlock (n : ℕ) := Fin (n / 16) → Fin (n + 1) → ℝ
abbrev Label (n : ℕ) := Fin (n / 16) → ℝ
abbrev History (N t : ℕ) := Fin t → Fin N
abbrev Cell (n : ℕ) := Σ J : ℕ, Fin n → Fin (2 ^ J)

instance cellMeasurableSpace (n : ℕ) : MeasurableSpace (Cell n) := ⊤

noncomputable def initialCube (n : ℕ) : Set (Coordinate n) :=
  Set.pi Set.univ (fun _ => Set.Ico (-1 / (2 * Real.sqrt n)) (1 / (2 * Real.sqrt n)))

noncomputable def cubePrior (n : ℕ) : Measure (Coordinate n) :=
  ProbabilityTheory.cond volume (initialCube n)

noncomputable def chart {n : ℕ} (z : Coordinate n) : Fin (n + 1) → ℝ :=
  Fin.lastCases (Real.sqrt (1 - ∑ a, (z a) ^ 2)) z

noncomputable def cellSet {n : ℕ} (Q : Cell n) : Set (Coordinate n) :=
  {z | ∀ a, -1 / (2 * Real.sqrt n) + (Q.2 a : ℝ) / (Real.sqrt n * (2 : ℝ) ^ Q.1) ≤ z a ∧
    z a < -1 / (2 * Real.sqrt n) + ((Q.2 a : ℝ) + 1) / (Real.sqrt n * (2 : ℝ) ^ Q.1)}

def rootCell (n : ℕ) : Cell n := ⟨0, fun _ => 0⟩

noncomputable def gaussianBlockLaw (n : ℕ) : Measure (GaussianBlock n) :=
  Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 1))

noncomputable def exactLabel {n : ℕ} (X : GaussianBlock n) (z : Coordinate n) : Label n :=
  fun row => ∑ a, X row a * chart z a

structure BlockRule (n N : ℕ) where
  prob : (GaussianBlock n × Label n) → Fin N → ℝ
  measurable_prob : ∀ w, Measurable (fun data => prob data w)
  nonneg : ∀ data w, 0 ≤ prob data w
  sum_one : ∀ data, ∑ w, prob data w = 1

abbrev Rules (n N t : ℕ) := ∀ i : Fin t, History N i.val → BlockRule n N

def past {N t : ℕ} (w : History N t) (i : Fin t) : History N i.val :=
  fun j => w ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

def through {N t : ℕ} (w : History N t) (i : Fin t) : History N (i.val + 1) :=
  fun j => w ⟨j.val, Nat.lt_of_lt_of_le j.isLt i.isLt⟩

noncomputable def blockProbability {n N : ℕ} (rule : BlockRule n N)
    (z : Coordinate n) (w : Fin N) : ℝ :=
  ∫ X, rule.prob (X, exactLabel X z) w ∂gaussianBlockLaw n

noncomputable def historyLikelihood {n N t : ℕ} (rules : Rules n N t)
    (z : Coordinate n) (w : History N t) : ℝ :=
  ∏ i, blockProbability (rules i (past w i)) z (w i)

noncomputable def experimentLaw {n N t : ℕ} (rules : Rules n N t) :
    Measure (Coordinate n × History N t) :=
  ∑ w : History N t,
    ((cubePrior n).withDensity (fun z => ENNReal.ofReal (historyLikelihood rules z w))).map
      (fun z => (z, w))

abbrev Disclosure (n N t : ℕ) := ∀ i : Fin t, Coordinate n → History N (i.val + 1) → Cell n

def ValidDisclosure {n N t : ℕ} (Q : Disclosure n N t) : Prop :=
  (∀ i, Measurable (fun zh : Coordinate n × History N (i.val + 1) => Q i zh.1 zh.2)) ∧
  (∀ i, (Set.range (fun zh : Coordinate n × History N (i.val + 1) => Q i zh.1 zh.2)).Finite) ∧
  (∀ z ∈ initialCube n, ∀ w : History N t, ∀ i,
    z ∈ cellSet (Q i z (through w i)) ∧ cellSet (Q i z (through w i)) ⊆ initialCube n) ∧
  (∀ z ∈ initialCube n, ∀ w : History N t, ∀ i j : Fin t, i ≤ j →
    cellSet (Q j z (through w j)) ⊆ cellSet (Q i z (through w i)))

noncomputable def transcriptMap {n N t : ℕ} (Q : Disclosure n N t)
    (zw : Coordinate n × History N t) : Coordinate n × (History N t × (Fin t → Cell n)) :=
  (zw.1, (zw.2, fun i => Q i zw.1 (through zw.2 i)))

noncomputable def augmentedLaw {n N t : ℕ} (rules : Rules n N t) (Q : Disclosure n N t) :=
  (experimentLaw rules).map (transcriptMap Q)

noncomputable def mutualInformation {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (α × β)) : ℝ≥0∞ :=
  InformationTheory.klDiv μ ((μ.map Prod.fst).prod (μ.map Prod.snd))

noncomputable def finalLevel {n N t : ℕ} (Q : Disclosure n N t)
    (zw : Coordinate n × History N t) : ℕ :=
  if ht : 0 < t then
    let i : Fin t := ⟨t - 1, by omega⟩
    (Q i zw.1 (through zw.2 i)).1
  else 0

def MainStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ C₀ : ℝ, 0 < C₀ →
    ∃ C : ℝ, 0 < C ∧ ∀ (n N t : ℕ), n₀ ≤ n → 1 ≤ N → ∀ rules : Rules n N t,
      (2 / (n / 8 : ℕ) + Real.exp (-c * (n / 16 : ℕ))) * Real.log N ≤ C₀ * (n + 1) →
      ∃ Q : Disclosure n N t, ValidDisclosure Q ∧
        mutualInformation (augmentedLaw rules Q) ≤ ENNReal.ofReal (C * (n + 1) * t) ∧
        (∫ zw, (finalLevel Q zw : ℝ) ∂experimentLaw rules) ≤ C * t

namespace FiniteEntropy

noncomputable def uniformCell {n : ℕ} (Q : Cell n) : Measure (Coordinate n) :=
  ProbabilityTheory.cond volume (cellSet Q)

def Descendant {n : ℕ} (Q R : Cell n) : Prop :=
  Q.1 ≤ R.1 ∧ cellSet R ⊆ cellSet Q

noncomputable def threshold (n h : ℕ) : ℝ := (2:ℝ)^(-(n:ℝ)*h/2)

def Heavy {n : ℕ} (P : Measure (Coordinate n)) (Q R : Cell n) : Prop :=
  Descendant Q R ∧ Q.1 < R.1 ∧ threshold n (R.1-Q.1) < (P (cellSet R)).toReal

def FirstHeavy {n : ℕ} (P : Measure (Coordinate n)) (Q R : Cell n) : Prop :=
  Heavy P Q R ∧ ∀ E : Cell n, Heavy P Q E → Descendant E R → E = R

noncomputable def residual {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) : Set (Coordinate n) :=
  cellSet Q \ ⋃ R : {R : Cell n // FirstHeavy P Q R}, cellSet R.val

abbrev Letter (n : ℕ) := Option (Cell n)
abbrev Log (n : ℕ) := List (Letter n)
instance logMeasurableSpace (n : ℕ) : MeasurableSpace (Log n) := ⊤

noncomputable def branch {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) : Letter n → Set (Coordinate n) := by
  classical
  exact fun
  | none => residual P Q
  | some R => if FirstHeavy P Q R then cellSet R else ∅

noncomputable def attemptLetter {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (z : Coordinate n) : Letter n := by
  classical
  exact if h : ∃ R : Cell n, FirstHeavy P Q R ∧ z ∈ cellSet R then some h.choose else none

structure State (n : ℕ) where
  cell : Cell n
  event : Set (Coordinate n)
  stopped : Bool

noncomputable def update {n : ℕ} (P : Measure (Coordinate n)) (s : State n) (a : Letter n) : State n :=
  if s.stopped then s else
  let μ := ProbabilityTheory.cond P s.event
  let E := branch μ s.cell a
  { cell := a.getD s.cell
    event := s.event ∩ E
    stopped := if a = none then decide ((1/2:ℝ) ≤ (μ E).toReal) else false }

noncomputable def state {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) : State n :=
  h.foldl (update P) ⟨Q,cellSet Q,false⟩

noncomputable def run {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) : ℕ → Coordinate n → Log n
  | 0, _ => []
  | N+1, z =>
    let h := run P Q N z
    let s := state P Q h
    if s.stopped then h else
      h ++ [attemptLetter (ProbabilityTheory.cond P s.event) s.cell z]

def Terminates {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (z : Coordinate n) : Prop :=
  ∃ N, (state P Q (run P Q N z)).stopped = true

noncomputable def attempts {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (z : Coordinate n) : ℕ := by
  classical
  exact if h : Terminates P Q z then Nat.find h else 0

noncomputable def terminalLog {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (z : Coordinate n) : Log n :=
  run P Q (attempts P Q z) z

noncomputable def terminalCell {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) : Cell n :=
  (state P Q h).cell

noncomputable def terminalLaw {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) : Measure (Coordinate n) :=
  ProbabilityTheory.cond P {z | terminalLog P Q z = h}

noncomputable def depth {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (z : Coordinate n) : ℕ :=
  (terminalCell P Q (terminalLog P Q z)).1-Q.1

def Regular {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) : Prop :=
  P (cellSet Q) = 1 ∧ ∀ R : Cell n, Descendant Q R → Q.1 < R.1 →
    (P (cellSet R)).toReal ≤ 2 * threshold n (R.1-Q.1)

def FiniteEntropyStatement : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ Q : Cell n, ∀ P : Measure (Coordinate n),
    IsProbabilityMeasure P → P ≪ uniformCell Q → InformationTheory.klDiv P (uniformCell Q) ≠ ∞ →
      (∀ᵐ z ∂P, Terminates P Q z) ∧ Measurable (terminalLog P Q) ∧
      (∀ h : Log n, P {z | terminalLog P Q z = h} ≠ 0 →
        Descendant Q (terminalCell P Q h) ∧ Regular (terminalLaw P Q h) (terminalCell P Q h)) ∧
      Integrable (fun z => (depth P Q z : ℝ)) P ∧
      Integrable (fun z => (attempts P Q z : ℝ)) P ∧
      (∫ z,(attempts P Q z : ℝ) ∂P) ≤ 2*(1+∫ z,(depth P Q z : ℝ) ∂P) ∧
      (∫⁻ z,InformationTheory.klDiv (terminalLaw P Q (terminalLog P Q z))
          (uniformCell (terminalCell P Q (terminalLog P Q z))) ∂P) +
        ENNReal.ofReal ((Real.log 2/4)*n*(∫ z,(depth P Q z : ℝ) ∂P)) ≤
          InformationTheory.klDiv P (uniformCell Q) + ENNReal.ofReal (2/Real.exp 1)



end FiniteEntropy
end RepeatedLocalization
end OAI


