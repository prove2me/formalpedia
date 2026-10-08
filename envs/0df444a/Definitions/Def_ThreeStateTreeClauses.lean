-- Prove2me | Definitions.Def_ThreeStateTreeClauses
-- name    : ThreeStateTreeClauses
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:31.289611+00:00
-- url     : https://prove2.me/theorems/32b471e7-2963-4c8e-bee4-8d052b6c5e56
-- statement:
--   The block sets up reconstruction of a root spin in a three-state broadcast process on a Galton–Watson-type tree. Spins take values in {0,1,2}. A parameter λ is admissible if −1/2 ≤ λ ≤ 1. The channel weight from spin i to spin j is (1+2λ)/3 if i = j and (1−λ)/3 otherwise; for admissible λ these are nonnegative, and for each i they sum to 1 over j, so each i has a channel distribution on spins. An observation at depth 0 is a spin, and an observation at depth ℓ+1 is a multiset of depth-ℓ observations. Given an offspring distribution on the natural numbers, observationLaw at depth 0 is the point mass at the root spin i. At depth ℓ+1 it draws a number n of children from the offspring law, then draws n independent child observations, each obtained by passing i through the channel to a child spin and then sampling that child's depth-ℓ observation law, and records them as a multiset. The joint weight of root spin i and observation o is (1/3) times this law, with a uniform prior on the root spin. The marginal weight sums the joint weight over i, and the posterior is their ratio. The advantage at depth ℓ is the marginal-weighted sum over observations of half the L1 distance between the posterior and the uniform (1/3,1/3,1/3) distribution. Reconstructs is the defined proposition that the advantage converges, as ℓ tends to infinity, to some strictly positive limit. The block also defines Poisson weights e^{−rate}·rate^k/k!, proves they are nonnegative and have total mass 1, and packages them as a Poisson distribution on the natural numbers for a given nonnegative real rate. It then opens a further Tree namespace.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThreeStateTreeClauses.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThreeStateTreeClauses.lean; bytes 16..3410
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open Filter

namespace ThreeState.TreeClauses

abbrev Spin := Fin 3

def Admissible (lam : ℝ) : Prop := -(1 / 2 : ℝ) ≤ lam ∧ lam ≤ 1

def channelWeight (lam : ℝ) (i j : Spin) : ℝ :=
  if i = j then (1 + 2 * lam) / 3 else (1 - lam) / 3

lemma channelWeight_nonneg {lam : ℝ} (hlam : Admissible lam) (i j : Spin) :
    0 ≤ channelWeight lam i j := by
  unfold channelWeight
  split_ifs <;> dsimp [Admissible] at hlam <;> linarith [hlam.1, hlam.2]

lemma channelWeight_sum (lam : ℝ) (i : Spin) : ∑ j, channelWeight lam i j = 1 := by
  fin_cases i <;> simp [channelWeight, Fin.sum_univ_three] <;> ring

def channel (lam : ℝ) (hlam : Admissible lam) (i : Spin) : PMF Spin :=
  PMF.ofFintype (fun j ↦ ENNReal.ofReal (channelWeight lam i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ channelWeight_nonneg hlam i j),
      channelWeight_sum]
    norm_num)

def Observation : ℕ → Type
  | 0 => Spin
  | n + 1 => Multiset (Observation n)

def iidList {α : Type} (p : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | n + 1 => p.bind fun x ↦ (iidList p n).map (List.cons x)

def observationLaw (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) :
    (ℓ : ℕ) → Spin → PMF (Observation ℓ)
  | 0, i => PMF.pure i
  | ℓ + 1, i => offspring.bind fun n ↦
      (iidList ((channel lam hlam i).bind (observationLaw lam hlam offspring ℓ)) n).map
        (fun xs ↦ (xs : Multiset (Observation ℓ)))

def jointWeight (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (i : Spin) (o : Observation ℓ) : ℝ≥0∞ :=
  (1 / 3 : ℝ≥0∞) * observationLaw lam hlam offspring ℓ i o

def marginalWeight (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (o : Observation ℓ) : ℝ≥0∞ :=
  ∑ i, jointWeight lam hlam offspring ℓ i o

def posterior (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (o : Observation ℓ) (i : Spin) : ℝ :=
  (jointWeight lam hlam offspring ℓ i o / marginalWeight lam hlam offspring ℓ o).toReal

def advantage (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) (ℓ : ℕ) : ℝ :=
  ∑' o : Observation ℓ, (marginalWeight lam hlam offspring ℓ o).toReal *
    ((∑ i : Spin, |posterior lam hlam offspring ℓ o i - (1 / 3 : ℝ)|) / 2)

def Reconstructs (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ Tendsto (advantage lam hlam offspring) atTop (nhds a)

namespace Probability

def poissonWeight (rate : ℝ) (count : ℕ) : ℝ :=
  Real.exp (-rate) * rate ^ count / (count.factorial : ℝ)

lemma poissonWeight_nonneg {rate : ℝ} (hrate : 0 ≤ rate) (count : ℕ) :
    0 ≤ poissonWeight rate count := by
  unfold poissonWeight
  positivity

lemma poissonWeight_mass (rate : ℝ≥0) : HasSum (poissonWeight rate) 1 :=
  ProbabilityTheory.hasSum_one_poissonMeasure rate

def _root_.OAI.ThreeState.TreeClauses.poissonPMF (rate : ℝ≥0) : PMF ℕ := by
  refine ⟨fun count ↦ ENNReal.ofReal (poissonWeight rate count), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← Real.toNNReal_one]
  exact (poissonWeight_mass rate).toNNReal (poissonWeight_nonneg rate.coe_nonneg)

end Probability

end ThreeState.TreeClauses

open scoped Topology
namespace ThreeState.TreeClauses.Tree



end ThreeState.TreeClauses.Tree
end
end OAI


