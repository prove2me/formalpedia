-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
-- name    : OAI_Combinatorics_CliqueFree_FiniteEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:46:47.246918+00:00
-- url     : https://prove2.me/theorems/1da98ffe-9989-4e9e-a0da-e0a1c6b49674
-- title:
--   Weighted entropy, relative entropy and total variation for finite probability vectors
-- statement:
--   Let $I$ be a finite index set and let $p,q,w\in\mathbb{R}^I$. Logarithms are natural. The file defines the following.
--
--   1. **Probability vector:** $p_i\ge 0$ for all $i$ and $\sum_{i\in I}p_i=1$.
--
--   2. **Weighted entropy** of $p$ relative to a weight vector $w$:
--
--      $$H_w(p)=\sum_{i\in I}p_i\log\frac{w_i}{p_i},$$
--
--      with the convention that terms with $p_i=0$ vanish. For $w\equiv 1$ this is the Shannon entropy of $p$; for positive $w$ it equals $-\sum_i p_i\log(p_i/w_i)$, the negative relative entropy of $p$ with respect to the unnormalised measure $w$.
--
--   3. **Relative entropy** (Kullback–Leibler divergence):
--
--      $$D(p\,\|\,q)=\sum_{i\in I}p_i\log\frac{p_i}{q_i},$$
--
--      intended for $q$ positive wherever $p$ is positive.
--
--   4. **Total variation distance:** $d_{\mathrm{TV}}(p,q)=\tfrac12\sum_{i\in I}|p_i-q_i|$.
--
--   These are the information-theoretic quantities used to analyse a random walk inside the neighbourhoods of a weighted graph. Weighted entropies of transition rows are measured against vertex weights; averaging rows raises weighted entropy by an average relative entropy, and relative entropies in turn control total-variation distances between rows.
--
--   **Formalization Note** The Lean names are `IsProb`, `entropy w p`, `divergence p q` and `tv p q`. Because `Real.log 0 = 0` and division by zero is zero in Lean, a term with $p_i=0$ is $0$, a term of $H_w$ with $w_i=0<p_i$ also evaluates to $0$, and a term of $D$ with $q_i=0<p_i$ evaluates to $0$; this is why the divergence is only used under the stated support condition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteEntropy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CliqueFreeLog mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteEntropy

variable {I : Type u} [Fintype I]

/-- A finite real-valued probability vector. -/
def IsProb (p : I → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Weighted row entropy, with the `0 log 0 = 0` convention. -/
def entropy (w p : I → ℝ) : ℝ := ∑ i, p i * Real.log (w i / p i)

/-- Relative entropy, used only when `q` is positive on the positive support of `p`. -/
def divergence (p q : I → ℝ) : ℝ := ∑ i, p i * Real.log (p i / q i)

/-- Total variation distance of two finite probability vectors. -/
def tv (p q : I → ℝ) : ℝ := (∑ i, |p i - q i|) / 2

variable {J : Type v} [Fintype J]

end FiniteEntropy

end CliqueFreeIndependence

end

end OAI


