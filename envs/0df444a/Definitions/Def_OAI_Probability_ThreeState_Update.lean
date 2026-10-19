-- Prove2me | Definitions.Def_OAI_Probability_ThreeState_Update
-- name    : OAI_Probability_ThreeState_Update
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:30:51.497445+00:00
-- url     : https://prove2.me/theorems/3bc1b13b-b631-4a5c-9592-dc31d6958ecc
-- title:
--   Belief-propagation update of three-spin messages through the symmetric channel
-- statement:
--   Throughout, a spin is an element of $\{0,1,2\}$. A parameter $\lambda\in\mathbb{R}$ is admissible if $-\tfrac12\le\lambda\le1$; then the symmetric channel $M_\lambda(i,j)=\tfrac{1+2\lambda}{3}$ for $j=i$ and $M_\lambda(i,j)=\tfrac{1-\lambda}{3}$ for $j\ne i$ is a stochastic matrix. Messages are vectors $m\in\mathbb{R}^3$ with nonnegative coordinates summing to $3$, and $\mathbf 1=(1,1,1)$ is the uninformative message.
--
--   1. **Edge message.** Passing a message $m$ through the channel gives
--   $$
--   E_\lambda(m)_i=1+\lambda\,(m_i-1),\qquad i\in\{0,1,2\}.
--   $$
--   This is again a message: admissibility of $\lambda$ makes it nonnegative, and its coordinates sum to $3$.
--   2. **Product weight and normalizer.** For messages $m^{(1)},\dots,m^{(n)}$ arriving from $n$ children,
--   $$
--   W_i=\prod_{j=1}^{n}E_\lambda\bigl(m^{(j)}\bigr)_i,\qquad Z=\frac13\sum_{i=0}^{2}W_i .
--   $$
--   Both are nonnegative, and $\sum_i W_i=3Z$.
--   3. **Combined message.** The parent's message is $W/Z=(W_0/Z,W_1/Z,W_2/Z)$ when $Z\ne0$, and the uninformative message $\mathbf 1$ when $Z=0$.
--
--   These are the belief-propagation recursions for the posterior of the root spin on a tree: children's likelihood messages are pushed through the edge channel, multiplied, and renormalized.
--
--   **Formalization Note** All three objects take the admissibility proof `h : Admissible lam` as an argument, because the edge message is a subtype element whose nonnegativity depends on it. Children are indexed by `Fin n`. Nonnegativity and the sum identity are stated as lemmas (`productWeight_nonneg`, `normalizer_nonneg`, `productWeight_sum`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/Update.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Update.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations
import Definitions.Def_OAI_Probability_ThreeState_Messages
import Definitions.Def_OAI_Probability_ThreeState_Observation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Branchwise likelihood updates and their independent product measures. -/

namespace ThreeState
open MeasureTheory
open scoped Classical

noncomputable def edgeMessage (lam : ℝ) (h : Admissible lam) (m : Message) : Message :=
  ⟨fun i => 1+lam*(m i-1), by
    constructor
    · intro i
      have hl := Message.nonneg m i
      have hu := Message.le_three m i
      by_cases hp : 0 ≤ lam
      · nlinarith [h.2]
      · have hn : lam ≤ 0 := le_of_not_ge hp
        nlinarith [h.1]
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Message.sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num⟩

 
noncomputable def productWeight (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) (i : Spin) : ℝ :=
  ∏ j, edgeMessage lam h (m j) i

noncomputable def normalizer (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) : ℝ :=
  (∑ i : Spin, productWeight lam h m i)/3

lemma productWeight_nonneg (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) (i : Spin) :
    0 ≤ productWeight lam h m i :=
  Finset.prod_nonneg (fun index _ => Message.nonneg (edgeMessage lam h (m index)) i)

lemma normalizer_nonneg (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) :
    0 ≤ normalizer lam h m := div_nonneg (Finset.sum_nonneg (fun i _ => productWeight_nonneg _ _ _ _)) (by norm_num)

lemma productWeight_sum (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) :
    ∑ i, productWeight lam h m i = 3*normalizer lam h m := by dsimp [normalizer]; ring

noncomputable def combineMessage (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) : Message :=
  if hz : normalizer lam h m = 0 then uninformative else
    ⟨fun i => productWeight lam h m i / normalizer lam h m, by
      constructor
      · intro i
        exact div_nonneg (productWeight_nonneg _ _ _ _) (normalizer_nonneg _ _ _)
      · rw [← Finset.sum_div, productWeight_sum]
        field_simp⟩

end ThreeState
namespace ThreeState
open MeasureTheory
open scoped Classical

end ThreeState

end OAI


