-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
-- name    : OAI_Probability_RandomSAT_FiniteMean
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:31:23.334344+00:00
-- url     : https://prove2.me/theorems/adbb1f35-1d36-4eaa-b99e-bc8ae43a97b7
-- title:
--   Uniform averages and variances over finite sets
-- statement:
--   For a finite set $A$ and a function $f:A\to\mathbb{R}$, this module defines the uniform average and the uniform variance.
--
--   1. **Uniform mean.**
--   $$
--   \mathbb{E}_A[f]=\frac{1}{|A|}\sum_{a\in A}f(a),
--   $$
--   the expectation of $f$ under the uniform distribution on $A$. It equals $0$ when $A$ is empty.
--   2. **Uniform variance.** $\operatorname{Var}_A[f]=\mathbb{E}_A\big[(f-\mathbb{E}_A[f])^2\big]$.
--
--   The module also records basic properties of the mean. It depends only on the values of $f$. The mean of a constant $c$ is $c$ when $A$ is nonempty, and the mean of the zero function is $0$. The mean is invariant under reindexing by a bijection $e:A\to B$, i.e. $\mathbb{E}_A[f\circ e]=\mathbb{E}_B[f]$. On a product it can be computed iteratively:
--   $$
--   \mathbb{E}_{A\times B}[f]=\mathbb{E}_{a\in A}\Big[\mathbb{E}_{b\in B}\big[f(a,b)\big]\Big].
--   $$
--
--   All probabilities in the random proper $k$-SAT model are finite uniform averages over clauses and formulas. The product rule lets a uniformly random formula be treated as a sequence of independent uniform clauses.
--
--   **Formalization Note** `uniformMean f` is the finite sum divided by `Fintype.card`, so the empty-set value $0$ comes from Lean's convention that division by zero is zero.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/FiniteMean.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/FiniteMean.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FixedClauseThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement

namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def uniformMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

theorem uniformMean_congr {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a = g a) : uniformMean f = uniformMean g := by
  unfold uniformMean
  congr 1
  exact Finset.sum_congr rfl (fun a _ => h a)

theorem uniformMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformMean (fun _ : α => c) = c := by
  simp [uniformMean, ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos :
    (0 : ℝ) < Fintype.card α)]

theorem uniformMean_zero {α : Type*} [Fintype α] :
    uniformMean (fun _ : α => (0 : ℝ)) = 0 := by
  simp [uniformMean]

theorem uniformMean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : uniformMean (fun a => f (e a)) = uniformMean f := by
  unfold uniformMean
  rw [e.sum_comp, Fintype.card_congr e]

theorem uniformMean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → ℝ) : uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b))) := by
  simp only [uniformMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

def uniformVariance {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  uniformMean (fun a => (f a - uniformMean f)^2)

end

end FixedClauseThreshold

end OAI


