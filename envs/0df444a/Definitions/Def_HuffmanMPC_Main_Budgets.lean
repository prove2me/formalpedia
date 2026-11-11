-- Prove2me | Definitions.Def_HuffmanMPC_Main_Budgets
-- name    : HuffmanMPC_Main_Budgets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:24:25.867802+00:00
-- url     : https://prove2.me/theorems/c5f8a857-f0d1-4bfb-b00c-d9392200e73d
-- title:
--   Problems 4.3 and 5.2 — budget-constrained optimum $\mu(I,b)$, relevant budgets, dyadic knapsack $\psi$, layered convexity of $G_b$
-- statement:
--   Fix depth bounds $\ell\le u$. For a frequency list $I$ and an integer budget $b$, the budget-constrained optimum is
--   $$\mu(I,b)=\min\Big\{\sum_{f_i\in I} f_ih_i:\ \sum_{f_i\in I}2^{u-h_i}\le b,\ h_i\in\{\ell,\dots,u\}\Big\},$$
--   with $\mu(I,b)=+\infty$ when no depth vector is feasible. The relevant budgets are $\mathcal B(I)=\{|I|,\dots,\min\{2^u,|I|2^{u-\ell}\}\}$.
--
--   The dyadic knapsack creates, for each occurrence $f_i\in I$, one item of each size $1,2,4,\dots,2^{u-\ell-1}$, all of value $f_i$; $\psi(I,c)$ is the largest total value of items of total size at most $c$.
--
--   For $A=A_1\uplus A_2$ and a budget $b$, $G_b(x)=\mu(A_1,x)+\mu(A_2,b-x)$. It is layered convex modulo $d\ge1$ when
--   $$G_b(x+2d)-G_b(x+d)\ \ge\ G_b(x+d)-G_b(x)$$
--   whenever $x+2d\le b$ and the three values are finite.
--
--   **Formalization Note** $\mu(I,b)$ takes values in $\mathbb N\cup\{\infty\}$, so an infeasible budget is $\infty$ and never a default $0$. The layered-convexity predicate compares only finite values, as integers, so no extended-value subtraction occurs.
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Problem 4.3 and Eq. (4), p. 15 (PDF 16); relevant budgets $\mathcal B(I)$, p. 18 (PDF 19); Definition 5.1, Problem 5.2, Eq. (6), pp. 20–21 (PDF 21–22)

import Definitions.Def_HuffmanMPC_Main_Coding

set_option autoImplicit false

namespace HuffmanMPC.Main

/-- Infeasible entries have value infinity, including an empty feasible set. -/
def BudgetFeasible (a : Frequencies) (lo hi b : ℕ) (h : Fin a.length → ℕ) : Prop :=
  (∀ i, lo ≤ h i ∧ h i ≤ hi) ∧ (∑ i, 2 ^ (hi - h i)) ≤ b

noncomputable def budgetOptimum (a : Frequencies) (lo hi b : ℕ) : ℕ∞ :=
  ⨅ h : {h : Fin a.length → ℕ // BudgetFeasible a lo hi b h},
    (depthCost a h.val : ℕ∞)

def budgetMax (a : Frequencies) (lo hi : ℕ) : ℕ :=
  min (2 ^ hi) (a.length * 2 ^ (hi - lo))

def relevantBudgets (a : Frequencies) (lo hi : ℕ) : Finset ℕ :=
  Finset.Icc a.length (budgetMax a lo hi)

/-- Each pair identifies an occurrence and one of its distinct upgrade items. -/
abbrev Upgrade (a : Frequencies) (lo hi : ℕ) := Fin a.length × Fin (hi - lo)

def upgradeWidth {a : Frequencies} {lo hi : ℕ} (j : Upgrade a lo hi) : ℕ := 2 ^ j.2.val

noncomputable def knapsackOptimum (a : Frequencies) (lo hi c : ℕ) : ℕ :=
  (Finset.univ.powerset.filter (fun s : Finset (Upgrade a lo hi) =>
    (∑ j ∈ s, upgradeWidth j) ≤ c)).sup fun s => ∑ j ∈ s, a[j.1]

/-- No extended-value subtraction: all three split costs must be finite. -/
def LayeredSplitConvex (a₁ a₂ : Frequencies) (lo hi b d : ℕ) : Prop :=
  0 < d ∧ ∀ x v₀ v₁ v₂ : ℕ,
    x + 2*d ≤ b →
    budgetOptimum a₁ lo hi x + budgetOptimum a₂ lo hi (b-x) = (v₀ : ℕ∞) →
    budgetOptimum a₁ lo hi (x+d) + budgetOptimum a₂ lo hi (b-(x+d)) = (v₁ : ℕ∞) →
    budgetOptimum a₁ lo hi (x+2*d) + budgetOptimum a₂ lo hi (b-(x+2*d)) = (v₂ : ℕ∞) →
    (v₂ : ℤ) - v₁ ≥ (v₁ : ℤ) - v₀

end HuffmanMPC.Main


