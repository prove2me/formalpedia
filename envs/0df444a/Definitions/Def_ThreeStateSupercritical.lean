-- Prove2me | Definitions.Def_ThreeStateSupercritical
-- name    : ThreeStateSupercritical
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:31.6658+00:00
-- url     : https://prove2.me/theorems/f6a1a7bb-1f12-4d9e-8820-f46197a43ac3
-- statement:
--   Spin is the three-element set Fin 3, and a parameter λ is Admissible when −1/2 ≤ λ ≤ 1. The noise channel channel(λ,i,j) equals (1+2λ)/3 when i=j and (1−λ)/3 when i≠j; for admissible λ every entry is nonnegative, and each row sums to 1 for any λ, so channelPMF(λ,i) is a probability distribution on Spin giving a noisy copy of spin i. Observation(n) is a type of depth-n observations: Observation(0) is Spin, and Observation(n+1) is the type of finite multisets of depth-n observations. For an offspring distribution on ℕ, observedLaw(offspring,λ,n,i) is the law of the depth-n observation of a root with spin i: at depth 0 it is the point mass at i; at depth n+1, an offspring number k is drawn, and then k independent children are generated, each by passing i through the channel to a noisy spin and then taking an independent depth-n observation from that spin, the results being collected as a multiset. With a uniformly random root spin, marginal is the resulting mixture law, posterior(law,y,i) is the Bayes posterior probability of spin i given observation y, taken to be 1/3 when y has marginal probability zero, and advantage(law) is the expected value over y of half the L¹ distance between the posterior and the uniform distribution (1/3,1/3,1/3). Special cases are regularLaw(b,λ,n), using the constant offspring number b, and poissonLaw(d,λ,n), using Poisson(d) offspring for d ≥ 0, with regularAdvantage and poissonAdvantage the corresponding advantages; poissonAdvantage requires d>1. Finally, Reconstructs(a) is the proposition that a real sequence a converges to some strictly positive limit L. These are definitions only; no theorem about when reconstruction holds is stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThreeStateSupercritical.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThreeStateSupercritical.lean; bytes 16..3197
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace ThreeState

abbrev Spin := Fin 3

 
def Admissible (lam : ℝ) : Prop := -(1 / 2 : ℝ) ≤ lam ∧ lam ≤ 1

 
noncomputable def channel (lam : ℝ) (i j : Spin) : ℝ :=
  if i = j then (1 + 2 * lam) / 3 else (1 - lam) / 3

 

def Observation : ℕ → Type
  | 0 => Spin
  | n + 1 => Multiset (Observation n)

theorem channel_nonneg {lam : ℝ} (h : Admissible lam) (i j : Spin) :
    0 ≤ channel lam i j := by
  unfold channel
  split_ifs
  · dsimp [Admissible] at h
    linarith [h.1]
  · dsimp [Admissible] at h
    linarith [h.2]

theorem channel_sum (lam : ℝ) (i : Spin) : ∑ j, channel lam i j = 1 := by
  fin_cases i <;> simp [channel, Fin.sum_univ_succ] <;> ring

noncomputable def channelPMF (lam : ℝ) (h : Admissible lam) (i : Spin) : PMF Spin :=
  PMF.ofFintype (fun j => ENNReal.ofReal (channel lam i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => channel_nonneg h i j)]
    simp [channel_sum])

 
noncomputable def iidList {α : Type*} (p : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | n + 1 => p.bind fun a => (iidList p n).map (List.cons a)

 

noncomputable def observedLaw (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    (n : ℕ) → Spin → PMF (Observation n)
  | 0, i => PMF.pure i
  | n + 1, i => offspring.bind fun k =>
      (iidList ((channelPMF lam h i).bind (observedLaw offspring lam h n)) k).map
        (fun xs : List (Observation n) => (xs : Multiset (Observation n)))

noncomputable def uniformSpin : PMF Spin := PMF.ofFintype (fun _ => 1 / 3) (by
  simp
  exact ENNReal.mul_inv_cancel (by norm_num) (by finiteness))

 
noncomputable def marginal {α : Type*} (law : Spin → PMF α) : PMF α :=
  uniformSpin.bind law

 
noncomputable def posterior {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) : ℝ :=
  if marginal law y = 0 then 1 / 3
  else (law i y).toReal / (3 * (marginal law y).toReal)

 

noncomputable def advantage {α : Type*} (law : Spin → PMF α) : ℝ :=
  ∑' y, (marginal law y).toReal *
    ((∑ i : Spin, |posterior law y i - 1 / 3|) / 2)

noncomputable def regularLaw (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) :=
  observedLaw (PMF.pure b) lam h n

 
noncomputable def poissonOffspring (d : ℝ) (hd : 0 ≤ d) : PMF ℕ := by
  refine ⟨fun k => ENNReal.ofReal (Real.exp (-d) * d ^ k / (k.factorial : ℝ)), ?_⟩
  apply ENNReal.hasSum_coe.2
  have hsum : HasSum (fun k : ℕ => Real.exp (-d) * d ^ k / (k.factorial : ℝ)) 1 :=
    ProbabilityTheory.hasSum_one_poissonMeasure ⟨d, hd⟩
  simpa using hsum.toNNReal (fun k => by positivity)

noncomputable def poissonLaw (d : ℝ) (hd : 0 ≤ d) (lam : ℝ)
    (h : Admissible lam) (n : ℕ) :=
  observedLaw (poissonOffspring d hd) lam h n

noncomputable def regularAdvantage (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) : ℝ :=
  advantage (regularLaw b lam h n)

noncomputable def poissonAdvantage (d : ℝ) (hd : 1 < d) (lam : ℝ)
    (h : Admissible lam) (n : ℕ) : ℝ :=
  advantage (poissonLaw d (le_trans (by norm_num) hd.le) lam h n)

 
def Reconstructs (a : ℕ → ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ Filter.Tendsto a Filter.atTop (nhds L)



end ThreeState
end OAI


