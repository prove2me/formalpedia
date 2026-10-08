-- Prove2me | Definitions.Def_GaussianInformation
-- name    : GaussianInformation
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:12.443994+00:00
-- url     : https://prove2.me/theorems/53f3dfe1-96cb-4b7e-983d-f9904d9a14dc
-- statement:
--   This block sets up a repeated-localization experiment on the n-sphere, and defines (without proving) a proposition MainStatement about information leakage. The unknown point is a coordinate vector z in R^n, with prior the uniform (conditional Lebesgue) measure on the cube [-1/(2√n), 1/(2√n))^n, and chart(z) lifts it to the unit vector (z, √(1−Σ z_a²)) in R^(n+1). Dyadic cells are pairs (J, index) giving a sub-cube of side 1/(√n 2^J); cellSet is the corresponding set of coordinates, rootCell is the whole cube, and cells carry the discrete σ-algebra. A Gaussian block is an (n/16)×(n+1) array of i.i.d. standard normals X, with exact label X·chart(z). A BlockRule with n and N is a measurable probability-vector-valued map from (X, label) to N possible answers; a family of Rules chooses a rule at each step i<t depending on the earlier history of answers. The probability of an answer under z averages the rule over X, the history likelihood multiplies these over steps, and experimentLaw is the joint law of (z, history) obtained by weighting the cube prior with that likelihood. A Disclosure assigns at each step a cell depending measurably on z and the history so far; ValidDisclosure requires finitely many values, that the cell contains z and lies inside the initial cube (for z in the cube), and that cells are nested decreasingly over time. The augmented law adds the disclosed cells to (z, history), mutualInformation is the KL divergence from a joint law to the product of its marginals, and finalLevel is the dyadic level of the last cell. MainStatement asserts that there exist c>0 and n₀ such that for every C₀>0 there is C>0 such that for all n≥n₀, N≥1, t and all rules satisfying (2/⌊n/8⌋ + exp(−c⌊n/16⌋)) log N ≤ C₀(n+1), some valid disclosure exists whose augmented-law mutual information between z and the history-plus-cells transcript is at most C(n+1)t, and whose expected final level under the experiment law is at most C t.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GaussianInformation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GaussianInformation.lean; bytes 16..4642
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



end RepeatedLocalization
end OAI


