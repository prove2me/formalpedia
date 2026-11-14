-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
-- name    : ConsistentSubmodular_Deterministic_Basic_SamplingOperators
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:05.100165+00:00
-- url     : https://prove2.me/theorems/6ba45432-a0dd-4ed9-9aa6-635edbdbf86d
-- title:
--   Independent sampling operators: subset weights, sample expectation $\mathbb E[v(S)]$ and $\mathbb E[v(B\cup S)]$
-- statement:
--   Let $\iota$ be a type with decidable equality, $U\subseteq\iota$ a finite set, $p:\iota\to\mathbb R$ a vector of probabilities, and $v$ a real function on finite subsets of $\iota$.
--
--   - `subsetWeight U p S`: the weight
--   $$\pi_U^p(S)=\prod_{i\in S}p_i\;\prod_{i\in U\setminus S}(1-p_i).$$
--   For $S\subseteq U$ and $p_i\in[0,1]$ on $U$ this is the probability that the random set drawn by including each $i\in U$ independently with probability $p_i$ equals $S$.
--   - `sampleExpectation U p v`: the expectation
--   $$\mathbb E_{S\sim(U,p)}\,v(S)=\sum_{S\subseteq U}\pi_U^p(S)\,v(S),$$
--   a sum over the power set of $U$.
--   - `sampleAdd U p v B`: the expectation after adding a fixed set $B$,
--   $$\mathbb E_{S\sim(U,p)}\,v(B\cup S)=\sum_{S\subseteq U}\pi_U^p(S)\,v(B\cup S).$$
--
--   The file also proves the basic facts that the weights are nonnegative on subsets of $U$ when $p\in[0,1]$ there, that the expectation is monotone in $v$ and additive, that it maps a constant function to the constant, and that for $U=\emptyset$ it evaluates $v$ at $\emptyset$ (respectively at $B$).
--
--   These operators are the general form of the expectation $\mathbb E[g(S)]$ over independent samples, used for mixture values $H_j(p)$ and for the multilinear extension $F_Q(z)$. They are the common basis of the comparison lemmas between mixtures and physical sampling in Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/SamplingOperators.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

def subsetWeight (U : Finset ι) (p : ι → ℝ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ U \ S, (1 - p i)

def sampleExpectation (U : Finset ι) (p : ι → ℝ) (v : Finset ι → ℝ) : ℝ :=
  ∑ S ∈ U.powerset, subsetWeight U p S * v S

theorem subsetWeight_nonnegative (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {S : Finset ι} (hS : S ⊆ U) :
    0 ≤ subsetWeight U p S := by
  exact mul_nonneg (Finset.prod_nonneg (fun i hi => (hp i (hS hi)).1))
    (Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (hp i (Finset.mem_sdiff.mp hi).1).2))

theorem sampleExpectation_mono (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {v w : Finset ι → ℝ}
    (h : ∀ S ⊆ U, v S ≤ w S) : sampleExpectation U p v ≤ sampleExpectation U p w := by
  apply Finset.sum_le_sum
  intro S hS
  have hSU := Finset.mem_powerset.mp hS
  exact mul_le_mul_of_nonneg_left (h S hSU) (subsetWeight_nonnegative U p hp hSU)

@[simp] theorem sampleExpectation_empty (p : ι → ℝ) (v : Finset ι → ℝ) :
    sampleExpectation ∅ p v = v ∅ := by simp [sampleExpectation, subsetWeight]

theorem sampleExpectation_add (U : Finset ι) (p : ι → ℝ) (v w : Finset ι → ℝ) :
    sampleExpectation U p (fun S => v S + w S) = sampleExpectation U p v + sampleExpectation U p w := by
  simp only [sampleExpectation, mul_add, Finset.sum_add_distrib]

@[simp] theorem sampleExpectation_const (U : Finset ι) (p : ι → ℝ) (c : ℝ) :
    sampleExpectation U p (fun _ => c) = c := by
  unfold sampleExpectation subsetWeight
  rw [← Finset.sum_mul, ← Finset.prod_add]
  simp

def sampleAdd (U : Finset ι) (p : ι → ℝ) (v : Finset ι → ℝ) (B : Finset ι) : ℝ :=
  sampleExpectation U p (fun S => v (B ∪ S))

@[simp] theorem sampleAdd_empty (p : ι → ℝ) (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd ∅ p v B = v B := by simp [sampleAdd]

end ConsistentSubmodular

end


