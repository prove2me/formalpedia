-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling
-- name    : ConsistentSubmodular_Deterministic_Basic_PhysicalSampling
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:09:02.580209+00:00
-- url     : https://prove2.me/theorems/9a3096de-1360-420f-aa32-ecee23079268
-- title:
--   Contracted objective $f_{B\mapsto\mathbb E[f(B\cup S)]}$ under independent sampling, and union probability $1-\prod(1-p_i)$
-- statement:
--   Let $f$ be an objective on $n$ elements (nonnegative, monotone and submodular, `Objective n`). Fix $U\subseteq\{0,\dots,n-1\}$ and probabilities $p:\{0,\dots,n-1\}\to\mathbb R$ with $p_i\in[0,1]$ for $i\in U$.
--
--   - `Objective.sampled f U p hp`: the objective
--   $$f_{U,p}(B)=\mathbb E_{S\sim(U,p)}\,f(B\cup S)=\sum_{S\subseteq U}\Big(\prod_{i\in S}p_i\prod_{i\in U\setminus S}(1-p_i)\Big)f(B\cup S),$$
--   that is, `sampleAdd U p f.value B`. Its structure fields are discharged: $f_{U,p}\ge 0$, $f_{U,p}$ is monotone, and $f_{U,p}(B\cup C)+f_{U,p}(B\cap C)\le f_{U,p}(B)+f_{U,p}(C)$. So contracting a finite independent sample preserves all axioms of an objective. The proofs use the pointwise submodularity inequality for the sets $B\cup S$ and $C\cup S$ and the monotonicity of the expectation.
--   - `unionProbability cores U p e`: for sets $O_i$ (`cores i`) indexed by $i\in U$ and an element $e$,
--   $$1-\prod_{i\in U}\begin{cases}1-p_i,& e\in O_i\\ 1,&\text{otherwise,}\end{cases}$$
--   the probability that $e$ lies in the union $\bigcup_{i\in I}O_i$ when each $i\in U$ is placed in $I$ independently with probability $p_i$. It equals $0$ for $U=\emptyset$, which the file records.
--
--   The first definition lets expected objectives be treated as objectives in their own right, in particular for the marginal value of a mixture over a buffer, and the second computes the marginals of the random union of candidate sets. Both serve the comparison between mixtures $H_Q(p)$ and the multilinear extension $F_Q(z(p))$ of Appendix B.2.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/PhysicalSampling.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalMap
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_CompatibleProfiles

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

namespace Objective

variable {n : ℕ} (f : Objective n)

/-- Contracting a finite independent sample preserves all objective axioms. -/
def sampled (U : Finset (Fin n)) (p : Fin n → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) : Objective n where
  value B := sampleAdd U p f.value B
  nonnegative B := by
    apply Finset.sum_nonneg
    intro S hS
    exact mul_nonneg (subsetWeight_nonnegative U p hp (Finset.mem_powerset.mp hS)) (f.nonnegative _)
  monotone B C hBC := sampleExpectation_mono U p hp (fun S _ =>
    f.monotone _ _ (Finset.union_subset_union_left hBC))
  submodular B C := by
    have hpoint (S : Finset (Fin n)) : f.value ((B ∪ C) ∪ S) + f.value ((B ∩ C) ∪ S) ≤
        f.value (B ∪ S) + f.value (C ∪ S) := by
      have hU : (B ∪ S) ∪ (C ∪ S) = (B ∪ C) ∪ S := by ext i; simp only [Finset.mem_union]; tauto
      have hI : (B ∪ S) ∩ (C ∪ S) = (B ∩ C) ∪ S := by ext i; simp only [Finset.mem_union, Finset.mem_inter]; tauto
      simpa only [hU, hI] using f.submodular (B ∪ S) (C ∪ S)
    have h := sampleExpectation_mono U p hp (fun S _ => hpoint S)
    simpa only [sampleAdd, sampleExpectation_add] using h

end Objective

variable {n : ℕ}

def unionProbability (cores : ι → Finset (Fin n)) (U : Finset ι) (p : ι → ℝ) (e : Fin n) : ℝ :=
  1 - ∏ i ∈ U, if e ∈ cores i then 1 - p i else 1

omit [DecidableEq ι] in
@[simp] theorem unionProbability_empty (cores : ι → Finset (Fin n)) (p : ι → ℝ) (e : Fin n) :
    unionProbability cores ∅ p e = 0 := by simp [unionProbability]

end ConsistentSubmodular

end


