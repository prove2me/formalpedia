-- Prove2me | Definitions.Def_AssortOpt_HMF_Supplement_TopTwoFamily
-- name    : AssortOpt_HMF_Supplement_TopTwoFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:15:57.456518+00:00
-- url     : https://prove2.me/theorems/743632ee-6a26-4625-8456-3f94b78c018e
-- title:
--   Theorem 4 — the geometric-price instance family and the top-2 lottery
-- statement:
--   Fix $M>0$ and $n$ items $1,\dots,n$ with prices $r_j=M^j$. The buyer's list has length at most two. Its most expensive item is $j$ with probability $M^{-j}$; the list is empty with probability $1-\sum_{j=1}^nM^{-j}$. If the most expensive item is $j>1$, it is the buyer's second choice and the first choice $j'$ is uniform on $\{1,\dots,j-1\}$; if it is $j=1$, the list is $(1)$. Hence
--   $$p(())=1-\sum_{j=1}^nM^{-j},\qquad p((1))=M^{-1},\qquad p((j',j))=\frac{M^{-j}}{j-1}\quad(1\le j'<j\le n).$$
--   A list distribution is an instance of this family when its positive support is exactly the set of lists of positive probability and its weights are these probabilities. The top-2 lottery is the budget-additive mechanism of Definition 17 with $w_j=1/2$ for all $j$ and $B=1$.
--
--   Items are `Fin n`, numbered from zero: Lean item $i$ is the paper's item $i+1$, so its price is $M^{i+1}$ and the list $(j',j)$ is `[j'-1, j-1]`.
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 25, Theorem 4; pp. 23–24, Definition 17 and top-k lotteries

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_BudgetRandom

namespace AssortOpt.HMF.Supplement
open Finset

/-- Theorem 4, p. 25: prices `r_j = M^j`. Items are 0-based, so Lean item `i` is the paper's
item `i + 1` and has price `M^(i+1)`. -/
def thm4Price {n : ℕ} (M : ℝ) (i : Fin n) : ℝ :=
  M ^ (i.val + 1)

/-- Theorem 4, p. 25: the list probabilities of the instance family (0-based items).
* `[]`: the empty list, with probability `1 - ∑_{j=1}^n M^{-j}`;
* `[0]`: the paper's list `(1)` (most expensive item `1`), with probability `M^{-1}`;
* `[a, b]` with `a < b`: the paper's most expensive item `j = b + 1 > 1` is the second choice and
  the first choice `j' = a + 1` is uniform on `{1, …, j - 1}`, so the probability is
  `M^{-j} / (j - 1) = M^{-(b+1)} / b`;
* every other list has probability `0`. -/
noncomputable def thm4Prob {n : ℕ} (M : ℝ) : List (Fin n) → ℝ
  | [] => 1 - ∑ i : Fin n, (M ^ (i.val + 1))⁻¹
  | [a] => if a.val = 0 then M⁻¹ else 0
  | [a, b] => if a < b then (M ^ (b.val + 1))⁻¹ / (b.val : ℝ) else 0
  | _ :: _ :: _ :: _ => 0

/-- `D` is the Theorem 4 instance with parameter `M`: its positive support is exactly the set of
lists of positive `thm4Prob M`-probability, and its weights are these probabilities. -/
def IsThm4Instance {n : ℕ} (M : ℝ) (D : ListDist n) : Prop :=
  (∀ ℓ ∈ D.supp, D.p ℓ = thm4Prob M ℓ) ∧ (∀ ℓ, 0 < thm4Prob M ℓ → ℓ ∈ D.supp)

/-- The top-2 lottery: the budget-additive mechanism of Definition 17 with `w_j = 1/2` and
`B = 1` (p. 24: "top-k lotteries is captured by setting `w_j = 1/k` for all `j` and `B = 1`"). -/
noncomputable def topTwoLottery {n : ℕ} : List (Fin n) → Fin n → ℝ :=
  budgetMech (fun _ => 1 / 2) 1

end AssortOpt.HMF.Supplement


