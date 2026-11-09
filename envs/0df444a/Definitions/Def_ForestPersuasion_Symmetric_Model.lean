-- Prove2me | Definitions.Def_ForestPersuasion_Symmetric_Model
-- name    : ForestPersuasion_Symmetric_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:18:01.736432+00:00
-- url     : https://prove2.me/theorems/288ec87d-ee0e-45b4-b30d-c2bc75ba9a44
-- title:
--   Schemes, descendant observations, Bayes posteriors and sender value
-- statement:
--   There are $n$ binary-action receivers and a binary state $\omega$. The common prior is $\mu=\Pr(\omega=1)\in(0,1)$. Receiver $i$ has four real payoffs $v_i(\omega,a)$, with adoption weakly preferable in state $1$ and strictly worse in state $0$. A valid model also has an acyclic forest hierarchy. The sender has a monotone nonnegative set utility $u(S)$, where $S$ is the set adopting.
--
--   For any signal type $M$, a scheme gives two probability mass functions on $M^n$. Receiver $i$ observes exactly the coordinates in $D_i$. Its posterior is the Bayes ratio of the corresponding whole-observation marginal probabilities. It adopts when the expected payoff from action $1$ is at least that from $0$, including equality. An impossible observation has posterior zero.
--
--   The state-conditional expectations and the ex ante value are
--   $$V(\Sigma)=\mu\,\mathbb E_{\Sigma(1)}u(S)+(1-\mu)\,\mathbb E_{\Sigma(0)}u(S).$$
--   The attainable-value set ranges over every signal type and every scheme. The optimal value $V^*$ is its supremum, independently of the LP definitions. Nonnegative expectations use extended nonnegative sums; boundedness of $u$ on its finite domain ensures their conversion to real loses no value. Thresholds are derived from the four receiver payoffs, never supplied as independent input. Symmetric utility means $u(S)=f(|S|)$.
--
--   These definitions preserve the hierarchical observation model, including correlation among messages and sender-favourable ties.
-- source:
--   Konstantin Zabarnyi, Designing Information in a Forest: Algorithmic Aspects, STOC 2027 submission #271 (October 2026; PDF dated November 2, 2026), §2, signaling scheme, information structure and optimization problem, PDF pp. 6–8 (printed pp. 5–7). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/271.pdf

import Mathlib
import Definitions.Def_ForestPersuasion_Symmetric_Hierarchy

noncomputable section
open scoped NNReal ENNReal
open Classical

namespace ForestPersuasion.Symmetric

/-- The real-valued persuasion data of §2; receiver utilities include both states and actions. -/
structure Model (n : ℕ) where
  hierarchy : Hierarchy n
  prior : ℝ
  receiverUtility : Fin n → Bool → Bool → ℝ

def Model.Valid {n : ℕ} (I : Model n) : Prop :=
  I.hierarchy.Valid ∧ 0 < I.prior ∧ I.prior < 1 ∧
    ∀ i, 0 ≤ I.receiverUtility i true true - I.receiverUtility i true false ∧
      I.receiverUtility i false true - I.receiverUtility i false false < 0

abbrev SenderUtility (n : ℕ) := Finset (Fin n) → ℝ≥0

def MonotoneUtility {n : ℕ} (u : SenderUtility n) : Prop :=
  ∀ S T, S ⊆ T → u S ≤ u T

/-- No restriction on the signal alphabet or on its cardinality. -/
abbrev Scheme (n : ℕ) (M : Type) := Bool → PMF (Fin n → M)

abbrev Observation {n : ℕ} (I : Model n) (M : Type) (i : Fin n) :=
  {j // j ∈ I.hierarchy.descendants i} → M

def observe {n : ℕ} (I : Model n) {M : Type} (i : Fin n) (s : Fin n → M) :
    Observation I M i := fun j => s j.val

/-- Marginal point probability of the whole descendant observation, not just the direct signal. -/
def observationMass {n : ℕ} (I : Model n) {M : Type} (σ : Scheme n M)
    (w : Bool) (i : Fin n) (o : Observation I M i) : ℝ≥0∞ :=
  ∑' s, if observe I i s = o then σ w s else 0

/-- Bayes' rule; the total division convention gives 0 on an impossible observation. -/
def posterior {n : ℕ} (I : Model n) {M : Type} (σ : Scheme n M)
    (i : Fin n) (s : Fin n → M) : ℝ :=
  let a := (observationMass I σ true i (observe I i s)).toReal
  let b := (observationMass I σ false i (observe I i s)).toReal
  I.prior * a / (I.prior * a + (1 - I.prior) * b)

/-- Action 1 is taken also at indifference. -/
def adopts {n : ℕ} (I : Model n) (i : Fin n) (p : ℝ) : Prop :=
  p * I.receiverUtility i true false + (1 - p) * I.receiverUtility i false false ≤
    p * I.receiverUtility i true true + (1 - p) * I.receiverUtility i false true

def adopters {n : ℕ} (I : Model n) {M : Type} (σ : Scheme n M)
    (s : Fin n → M) : Finset (Fin n) :=
  Finset.univ.filter (fun i => adopts I i (posterior I σ i s))

/-- Nonnegative expectations are taken in ENNReal before conversion to real.
They are finite since u has finite domain. -/
def stateValue {n : ℕ} (I : Model n) (u : SenderUtility n) {M : Type}
    (σ : Scheme n M) (w : Bool) : ℝ :=
  (∑' s, σ w s * (u (adopters I σ s) : ℝ≥0∞)).toReal

def value {n : ℕ} (I : Model n) (u : SenderUtility n) {M : Type}
    (σ : Scheme n M) : ℝ :=
  I.prior * stateValue I u σ true + (1 - I.prior) * stateValue I u σ false

/-- Supremum over actual schemes over arbitrary small signal types, independent of every LP. -/
def attainableValues {n : ℕ} (I : Model n) (u : SenderUtility n) : Set ℝ :=
  {v | ∃ (M : Type) (σ : Scheme n M), value I u σ = v}

def Vstar {n : ℕ} (I : Model n) (u : SenderUtility n) : ℝ :=
  sSup (attainableValues I u)

/-- Derived from the four receiver payoffs, as in §2, PDF p. 8. -/
def threshold {n : ℕ} (I : Model n) (i : Fin n) : ℝ :=
  let a := I.receiverUtility i true true - I.receiverUtility i true false
  let b := I.receiverUtility i false false - I.receiverUtility i false true
  b / (a + b)

/-- Cardinalities belong to 0,...,n, including for n = 0. -/
def symmetricUtility {n : ℕ} (f : Fin (n + 1) → ℝ≥0) : SenderUtility n :=
  fun S => f ⟨S.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ S)⟩

end ForestPersuasion.Symmetric


