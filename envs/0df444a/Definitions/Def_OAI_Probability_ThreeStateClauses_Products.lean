-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_Products
-- name    : OAI_Probability_ThreeStateClauses_Products
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:42:19.08822+00:00
-- url     : https://prove2.me/theorems/b13ea96e-d737-4830-84c6-41954f573d57
-- title:
--   Independent product of finitely many discrete laws
-- statement:
--   Let $\alpha$ be a type and $n\in\mathbb{N}$.
--
--   1. **Product sums.** For functions $f_0,\dots,f_{n-1}:\alpha\to[0,\infty]$,
--   $$
--   \sum_{v\in\alpha^n}\ \prod_{j<n}f_j(v_j)=\prod_{j<n}\ \sum_{a\in\alpha}f_j(a).
--   $$
--   2. **Product law.** For discrete probability distributions $p_0,\dots,p_{n-1}$ on $\alpha$, the product law on $\alpha^n$ has mass
--   $$
--   P(v)=\prod_{j<n}p_j(v_j),
--   $$
--   which sums to $1$ by the previous identity. It is the law of a tuple of independent draws $v_j\sim p_j$.
--
--   Product laws model the independent subtrees below a vertex with a fixed, ordered set of children.
--
--   **Formalization Note** `productPMF p` is a probability mass function on `Fin n → α`. The summation identity `ennreal_tsum_fin_product` is stated for $[0,\infty]$-valued sums.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/Products.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/Products.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateTreeClauses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Products. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment

variable {α β : Type*}

lemma ennreal_tsum_fin_product (n : ℕ) (f : Fin n → α → ℝ≥0∞) :
    (∑' v : Fin n → α, ∏ j, f j (v j)) = ∏ j, ∑' a, f j a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) ↦ α)).tsum_eq]
    change (∑' z : α × (Fin n → α), ∏ j, f j (Fin.cons (α := fun _ : Fin (n+1) ↦ α) z.1 z.2 j)) = _
    simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod' (f := fun z : α × (Fin n → α) ↦ f 0 z.1*∏ j, f j.succ (z.2 j))]
    simp_rw [ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right]

def productPMF {n : ℕ} (p : Fin n → PMF α) : PMF (Fin n → α) :=
  ⟨fun v ↦ ∏ j, p j (v j), ENNReal.summable.hasSum_iff.2 (by
    rw [ennreal_tsum_fin_product]
    simp only [PMF.tsum_coe, Finset.prod_const_one])⟩

@[simp] lemma productPMF_apply {n : ℕ} (p : Fin n → PMF α) (v : Fin n → α) :
    productPMF p v = ∏ j, p j (v j) := rfl

end ThreeState.TreeClauses.Experiment

end

end OAI


