-- Prove2me | Definitions.Def_OnlineCRS_Knapsack_Model
-- name    : OnlineCRS_Knapsack_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:08.747412+00:00
-- url     : https://prove2.me/theorems/46b3301d-346a-42b8-b867-a84a27062f3f
-- title:
--   Section 2.3 — knapsack polytope and the randomized big/small greedy family
-- statement:
--   Fix a finite ground set $N$ and element sizes $s_e\in[0,1]$. The **knapsack polytope** and its feasible sets are
--
--   $$P=\{x\in[0,1]^N:\sum_{e\in N}s_ex_e\le1\},\qquad \mathcal F=\{I\subseteq N:\sum_{e\in I}s_e\le1\}.$$
--
--   The **big elements** are $N_{\mathrm{big}}=\{e:s_e>1/2\}$, with fractional load $b_{\mathrm{big}}=\sum_{e\in N_{\mathrm{big}}}s_ex_e$. The construction chooses the family of feasible subsets of $N_{\mathrm{big}}$ with probability $p_{\mathrm{big}}=(1-2b+2b_{\mathrm{big}})/(2-2b)$, and otherwise chooses the family of feasible subsets of $N\setminus N_{\mathrm{big}}$.
--
--   This is the specific randomized greedy family analyzed in Theorem 2.9.
--
--   **Formalization Note** Outside $x\in bP$, where the paper never uses the scheme, the mixing probability is set to zero so the weight map is a distribution on every input. The two family weights are added when the families coincide.
-- source:
--   arXiv:1508.00142v2, §2.3 and proof of Theorem 2.9, pp. 14–15

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics

namespace OnlineCRS.Knapsack

open scoped Pointwise

/-- The natural fractional relaxation of a unit-capacity knapsack (§2.3, p. 14). -/
def knapsackPolytope {α : Type} [Fintype α] (s : α → ℝ) : Set (α → ℝ) :=
  {x | (∀ e, 0 ≤ x e ∧ x e ≤ 1) ∧ ∑ e, s e * x e ≤ 1}

/-- The feasible subsets of a unit-capacity knapsack (§2.3, p. 14). -/
def knapsackFeasible {α : Type} [DecidableEq α] (s : α → ℝ) (I : Finset α) : Prop :=
  ∑ e ∈ I, s e ≤ 1

open Classical in
/-- The big elements `N_big = {e : s_e > 1/2}` (proof of Theorem 2.9, p. 14). -/
noncomputable def bigElements {α : Type} [Fintype α] [DecidableEq α] (s : α → ℝ) : Finset α :=
  Finset.univ.filter (fun e => 1 / 2 < s e)

/-- The fractional load `b_big = ∑_{e∈N_big} s_e x_e` (proof of Theorem 2.9, p. 14). -/
noncomputable def bigLoad {α : Type} [Fintype α] [DecidableEq α]
    (s x : α → ℝ) : ℝ := ∑ e ∈ bigElements s, s e * x e

/-- The probability `p_big = (1 - 2b + 2b_big)/(2 - 2b)` (proof of Theorem 2.9, p. 14). -/
noncomputable def bigProbability {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (b : ℝ) (x : α → ℝ) : ℝ :=
  (1 - 2 * b + 2 * bigLoad s x) / (2 - 2 * b)

open Classical in
/-- The feasible subsets using only big elements (proof of Theorem 2.9, pp. 14–15). -/
noncomputable def bigFamily {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) : Finset (Finset α) :=
  Finset.univ.filter (fun I => I ⊆ bigElements s ∧ knapsackFeasible s I)

open Classical in
/-- The feasible subsets using only small elements (proof of Theorem 2.9, pp. 14–15). -/
noncomputable def smallFamily {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) : Finset (Finset α) :=
  Finset.univ.filter (fun I => (∀ e ∈ I, e ∉ bigElements s) ∧ knapsackFeasible s I)

open Classical in
/-- The proof's mixing probability on `b • P`. Outside the input domain the choice is the
small-element family, making the randomized scheme a probability distribution on every `x`. -/
noncomputable def mixProbability {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (b : ℝ) (x : α → ℝ) : ℝ :=
  if x ∈ b • knapsackPolytope s then bigProbability s b x else 0

/-- The random choice of the big or small greedy family; the two indicator contributions add
even when the families coincide (proof of Theorem 2.9, pp. 14–15). -/
noncomputable def knapsackWeights {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (b : ℝ) (x : α → ℝ) (Fam : Finset (Finset α)) : ℝ :=
  (if Fam = bigFamily s then mixProbability s b x else 0) +
    (if Fam = smallFamily s then 1 - mixProbability s b x else 0)

end OnlineCRS.Knapsack


