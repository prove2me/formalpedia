-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
-- name    : OAI_Probability_ThreeStateClauses_DiscreteLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:41:44.349787+00:00
-- url     : https://prove2.me/theorems/b579233f-14a0-4f6e-b3a9-d902d6bb7687
-- title:
--   Uniform spin prior, marginal law and posterior message of a three-hypothesis experiment
-- statement:
--   Let $\alpha$ be a type and $p=(p_0,p_1,p_2)$ three discrete probability distributions on $\alpha$: the laws of an observation under the three possible spins.
--
--   1. **Uniform prior.** The uniform distribution on $\{0,1,2\}$, giving each spin mass $\tfrac13$.
--   2. **Marginal law.** $\bar p=\frac13(p_0+p_1+p_2)$, the law of the observation when the spin is uniform.
--   3. **Weight.** $w(a)=\frac13\bigl(p_0(a)+p_1(a)+p_2(a)\bigr)\ge0$, the marginal mass of $a$ as a real number.
--   4. **Posterior message.** For an observation $a$,
--   $$
--   m(a)=\Bigl(\frac{p_0(a)}{w(a)},\frac{p_1(a)}{w(a)},\frac{p_2(a)}{w(a)}\Bigr)\quad\text{if }w(a)\ne0,\qquad m(a)=(1,1,1)\ \text{ otherwise}.
--   $$
--   This is a message: its coordinates are nonnegative with average $1$, and $m_i(a)/3$ is the posterior probability of spin $i$ given $a$.
--   5. **Law of the message.** For countable $\alpha$ with measurable singletons, this is the probability measure on the message set obtained by pushing $\bar p$ forward under $a\mapsto m(a)$.
--
--   The law of the posterior message summarizes the experiment completely for the purpose of estimating the spin. Comparisons and limits of experiments are carried out on these laws.
--
--   **Formalization Note** The names are `uniformSpin`, `discreteMarginal`, `discreteWeight`, `discreteMessage` and `discreteProbability`. Probabilities in `PMF` are extended nonnegative reals and are converted with `toReal`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/DiscreteLaw.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/DiscreteLaw.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateTreeClauses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Discrete Law. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α : Type*}

def uniformSpin : PMF (Fin 3) := PMF.ofFintype (fun _ ↦ (1/3 : ℝ≥0∞)) (by
  norm_num
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

@[simp] lemma uniformSpin_apply (i : Fin 3) : uniformSpin i = (1/3 : ℝ≥0∞) := rfl

def discreteMarginal (p : Fin 3 → PMF α) : PMF α := uniformSpin.bind p

def discreteWeight (p : Fin 3 → PMF α) (a : α) : ℝ := avg (fun i ↦ (p i a).toReal)

lemma discreteWeight_nonneg (p : Fin 3 → PMF α) (a : α) : 0 ≤ discreteWeight p a := by
  unfold discreteWeight avg; positivity

def discreteMessage (p : Fin 3 → PMF α) (a : α) : Message := by
  by_cases h : discreteWeight p a = 0
  · exact ⟨fun _ ↦ 1, fun _ ↦ by norm_num, by norm_num [avg]⟩
  · refine ⟨fun i ↦ (p i a).toReal/discreteWeight p a, fun _ ↦ div_nonneg (by positivity)
      (discreteWeight_nonneg p a), ?_⟩
    change ((p 0 a).toReal/discreteWeight p a+(p 1 a).toReal/discreteWeight p a+
      (p 2 a).toReal/discreteWeight p a)/3 = 1
    rw [← add_div, ← add_div, div_div, mul_comm]
    have hw : (p 0 a).toReal+(p 1 a).toReal+(p 2 a).toReal = 3*discreteWeight p a := by
      dsimp [discreteWeight, avg]; ring
    rw [hw, div_self (mul_ne_zero (by norm_num) h)]

section Measures
variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

def discreteProbability (p : Fin 3 → PMF α) : ProbabilityMeasure Message :=
  ProbabilityMeasure.map (⟨(discreteMarginal p).toMeasure, inferInstance⟩ : ProbabilityMeasure α)
    (f := discreteMessage p) (measurable_of_countable _).aemeasurable

end Measures

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

end ThreeState.TreeClauses.Experiment

end

end OAI


