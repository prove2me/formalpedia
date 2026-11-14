-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation
-- name    : ConsistentSubmodular_Deterministic_Basic_FiniteExpectation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:09.716981+00:00
-- url     : https://prove2.me/theorems/2e18a5fb-7016-4686-a7a7-dae3f2dc272e
-- title:
--   Independent-Bernoulli weights and finite expectation over subsets
-- statement:
--   Let $\iota$ be a finite type with decidable equality, $p:\iota\to\mathbb R$ a family of probabilities, and $v$ a real function on subsets of $\iota$.
--
--   - `bernoulliWeight p S` $=\prod_{i\in S}p_i\cdot\prod_{i\notin S}(1-p_i)$: the probability that the random set containing each $i$ independently with probability $p_i$ equals $S$ (a plain real number defined for arbitrary $p$, with no range assumption).
--   - `finiteExpectation p v` $=\sum_{S\subseteq\iota}\mathrm{bernoulliWeight}(p,S)\,v(S)$: the expectation $\mathbb E[v(I(p))]$ of $v$ at the random set $I(p)$.
--
--   The file also proves the basic facts: weights are nonnegative when $0\le p_i\le1$, they sum to $1$ for every $p$, the expectation is monotone in $v$ for $p\in[0,1]^\iota$, and the expectation of a constant function is that constant.
--
--   These notions give the multilinear value of a mixture of types (the quantity $H_j(p)$ of equation (3)) in the deterministic part of the development, where it is evaluated along polygonal paths in the simplex.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/FiniteExpectation.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bernoulliWeight (p : ι → ℝ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ Sᶜ, (1 - p i)

def finiteExpectation (p : ι → ℝ) (v : Finset ι → ℝ) : ℝ :=
  ∑ S : Finset ι, bernoulliWeight p S * v S

theorem bernoulliWeight_nonnegative (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset ι) : 0 ≤ bernoulliWeight p S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i _ => (hp i).1)
  · exact Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hp i).2)

theorem sum_bernoulliWeight (p : ι → ℝ) : (∑ S : Finset ι, bernoulliWeight p S) = 1 := by
  unfold bernoulliWeight
  rw [← Fintype.prod_add]
  simp

theorem finiteExpectation_mono (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {v w : Finset ι → ℝ} (h : ∀ S, v S ≤ w S) :
    finiteExpectation p v ≤ finiteExpectation p w := by
  exact Finset.sum_le_sum (fun S _ => mul_le_mul_of_nonneg_left (h S) (bernoulliWeight_nonnegative p hp S))

@[simp] theorem finiteExpectation_const (p : ι → ℝ) (c : ℝ) :
    finiteExpectation p (fun _ => c) = c := by
  unfold finiteExpectation
  rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

end ConsistentSubmodular

end


