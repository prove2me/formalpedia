-- Prove2me | Definitions.Def_OAI_Combinatorics_PerfectMatching_Covariance
-- name    : OAI_Combinatorics_PerfectMatching_Covariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:54:48.680981+00:00
-- url     : https://prove2.me/theorems/f37a1545-19e3-4ada-aa92-81da5a17f526
-- title:
--   Weighted Gram matrices, direction spans and normalized centered vectors
-- statement:
--   Let $A$ be a finite set of outcomes and $I$ a finite set of coordinates, let $p\in\mathbb{R}^A$ be a weight vector and let $b=(b_a)_{a\in A}$ be a family of vectors $b_a\in\mathbb{R}^I$.
--
--   1. *Weighted columns.* $W(p,b)\in\mathbb{R}^{I\times A}$ is the matrix with entries $W_{i a}=\sqrt{p_a}\,b_a(i)$.
--   2. *Covariance (Gram) matrix.*
--   $$
--   C(p,b)=W(p,b)\,W(p,b)^{\top},\qquad C(p,b)_{ij}=\sum_{a\in A}p_a\,b_a(i)\,b_a(j)\quad\text{when }p\ge0 .
--   $$
--   When $p$ is a probability vector, it is the second-moment matrix of the random vector $b_a$ for $a$ distributed according to $p$. If moreover the vectors $b_a$ are centered at their $p$-mean, it is their covariance matrix.
--   3. *Weighted direction space.* $\operatorname{span}\{b_a: a\in A,\ p_a>0\}\subseteq\mathbb{R}^I$, the span of the vectors charged by $p$.
--   4. *Normalized centered vectors.* For $v=(v_a)_{a\in A}$ with $v_a\in\mathbb{R}^I$ and $x\in\mathbb{R}^I$,
--   $$
--   \tilde v_a(i)=\frac{v_a(i)-x_i}{\sqrt{x_i}} .
--   $$
--
--   These matrices are positive semidefinite by construction. For $p\ge0$ their column space is the weighted direction space, so the rank equals its dimension. They are the objects of the spectral argument relating rank, trace and a quadratic second-variation inequality. Suppose $p$ is a probability vector and the $v_a$ are $0/1$ vectors whose $p$-mean is $x$, with all $x_i>0$. Then the normalization makes the diagonal entries of $C(p,\tilde v)$ equal to $1-x_i$, so its trace is $|I|-\sum_i x_i$.
--
--   **Formalization Note** The names are `weightedColumns`, `covariance`, `weightedDirectionSpace` and `normalizedCentered`. Lean's square root sends negative numbers to $0$, so in general $C(p,b)_{ij}=\sum_a\max(p_a,0)\,b_a(i)\,b_a(j)$. Division by $0$ gives $0$, so coordinates with $x_i\le0$ of a normalized centered vector are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Covariance.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Covariance.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face

namespace OAI

/-!
Positive semidefinite covariance matrices, rank, trace, and a spectral inequality.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

def weightedColumns (p : A → ℝ) (b : A → I → ℝ) : Matrix I A ℝ :=
  fun i a => Real.sqrt (p a) * b a i

def covariance (p : A → ℝ) (b : A → I → ℝ) : Matrix I I ℝ :=
  weightedColumns p b * (weightedColumns p b)ᵀ

def weightedDirectionSpace (p : A → ℝ) (b : A → I → ℝ) : Submodule ℝ (I → ℝ) :=
  Submodule.span ℝ (Set.range fun a : {a // 0 < p a} => b a.val)

def normalizedCentered (v : A → I → ℝ) (x : I → ℝ) (a : A) (i : I) : ℝ :=
  (v a i-x i)/Real.sqrt (x i)

end MatchingEntropy

end

end OAI


