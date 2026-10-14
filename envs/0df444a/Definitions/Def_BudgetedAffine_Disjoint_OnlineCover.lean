-- Prove2me | Definitions.Def_BudgetedAffine_Disjoint_OnlineCover
-- name    : BudgetedAffine_Disjoint_OnlineCover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T21:16:55.686778+00:00
-- url     : https://prove2.me/theorems/34e0cd6b-c7ca-442d-8bd3-fd5d54dc6c50
-- title:
--   Sec. 4.1, (4.2)–(4.4) — online fractional covering algorithm with competitive ratio ρ, online and greedy augmenting costs
-- statement:
--   **Online fractional covering.** Fix a matrix $M\in\mathbb R^{m\times n}$ and costs $d\in\mathbb R^n$, and write $\Theta(h)=\min_{y\ge0}\{d^Ty : My\ge h\}$ for the offline covering value. In the online problem, sets of rows $S_1,S_2,\dots\subseteq[m]$ arrive one at a time; when $S_r$ arrives, the algorithm must augment its current solution so that $(My)_i\ge1$ for every $i\in S_r$, and it can never decrease a variable.
--
--   An **online covering algorithm with competitive ratio $\rho$** assigns to every revealed sequence $s=(S_1,\dots,S_r)$ a vector $y^{\mathcal A}_s\in\mathbb R^n$ (depending only on what has been revealed) such that
--   1. $y^{\mathcal A}_{()}=0$ and $y^{\mathcal A}_s\ge0$;
--   2. $y^{\mathcal A}_s\le y^{\mathcal A}_{(s,S)}$ for every next set $S$ (decisions are never revoked);
--   3. if the rows $S_1\cup\dots\cup S_r$ can be covered at all, then $(My^{\mathcal A}_s)_i\ge1$ for every revealed row $i$;
--   4. for every sequence of pairwise disjoint sets whose union can be covered,
--   $$\mathcal A(S_1,\dots,S_r):=d^Ty^{\mathcal A}_s\ \le\ \rho\cdot\Theta\Big(\sum_{r'}\mathbb 1(S_{r'})\Big).$$
--
--   The **online augmenting cost** (4.2) is $\mathcal A(S\mid s)=\mathcal A(s,S)-\mathcal A(s)$, and the **greedy augmenting cost** (4.3) is
--   $$\mathrm{Aug}(S\mid s)=\min_{y\ge0}\big\{d^Ty\ :\ M(y+y^{\mathcal A}_s)\ge\mathbb 1(S)\big\}.$$
--
--   This is the interface of the online algorithm the paper uses: Buchbinder and Naor's algorithm is such an algorithm with $\rho=O(\log n)$, which is the paper's (4.4).
--
--   **Formalization Note** The algorithm is an abstract structure, not Buchbinder–Naor's specific scheme; the paper uses only the properties listed. Coverage and competitiveness are required only when the revealed rows are coverable (otherwise no algorithm could exist); the competitive bound is stated for disjoint batches, as in the paper's Notations (p. 15). $\Theta$ and $\mathrm{Aug}$ are extended-real infima ($+\infty$ when infeasible). The requirement $y^{\mathcal A}_{()}=0$ is the paper's implicit $\nu_0=0$.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Sec. 4.1, (4.2), (4.3), (4.4), pp. 15–16

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model

namespace BudgetedAffine.Disjoint

open Matrix

/-- The union `S₁ ∪ ⋯ ∪ S_r` of a sequence of requirement sets. -/
def reqUnion {m : ℕ} (s : List (Finset (Fin m))) : Finset (Fin m) :=
  s.foldr (· ∪ ·) ∅

/-- An online algorithm for the online fractional covering problem
`min {dᵀy | M y ≥ 𝟙, y ≥ 0}` whose rows arrive in batches `S₁, S₂, …` (Sec. 4.1), with
competitive ratio `ρ`.

* `sol s` is the algorithm's current solution after the requirement sequence `s` has been
  revealed; it depends on the revealed prefix only.
* It starts from `0`, stays non-negative, and is only ever augmented (`mono`).
* Whenever the revealed rows can be covered at all, every revealed row is covered.
* On every sequence of pairwise disjoint batches whose union can be covered, its cost is at most
  `ρ` times the offline optimum `Θ(∑ᵣ 𝟙(Sᵣ))` (eq. (4.4) with `O(log n)` written as `ρ`). -/
structure OnlineCover {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ) (ρ : ℝ) where
  /-- The online solution `y^A` after the requirement sequence. -/
  sol : List (Finset (Fin m)) → Fin n → ℝ
  sol_nil : sol [] = 0
  nonneg : ∀ s, 0 ≤ sol s
  mono : ∀ s S, sol s ≤ sol (s ++ [S])
  covers : ∀ s, BudgetedAffine.Budget.coverCost M d (BudgetedAffine.Budget.indic (reqUnion s)) ≠ ⊤ →
    ∀ S ∈ s, ∀ i ∈ S, 1 ≤ (M *ᵥ sol s) i
  compet : ∀ s, s.Pairwise Disjoint → BudgetedAffine.Budget.coverCost M d (BudgetedAffine.Budget.indic (reqUnion s)) ≠ ⊤ →
    ((d ⬝ᵥ sol s : ℝ) : EReal) ≤ (ρ : EReal) * BudgetedAffine.Budget.coverCost M d (BudgetedAffine.Budget.indic (reqUnion s))

variable {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ} {d : Fin n → ℝ} {ρ : ℝ}

/-- The online cost `A(h₁, …, h_r) = dᵀ y^A`. -/
def OnlineCover.cost (alg : OnlineCover M d ρ) (s : List (Finset (Fin m))) : ℝ :=
  d ⬝ᵥ alg.sol s

/-- The online augmenting cost (4.2): `A(S | s) = A(s, S) − A(s)`. -/
def OnlineCover.augCost (alg : OnlineCover M d ρ) (s : List (Finset (Fin m)))
    (S : Finset (Fin m)) : ℝ :=
  alg.cost (s ++ [S]) - alg.cost s

/-- The greedy augmenting cost (4.3):
`Aug(S | s) = min_{y ≥ 0} {dᵀy | M (y + y^A_s) ≥ 𝟙(S)}`, in `EReal` (`+∞` when infeasible). -/
noncomputable def OnlineCover.greedyAug (alg : OnlineCover M d ρ) (s : List (Finset (Fin m)))
    (S : Finset (Fin m)) : EReal :=
  ⨅ (y : Fin n → ℝ) (_ : 0 ≤ y ∧ BudgetedAffine.Budget.indic S ≤ M *ᵥ (y + alg.sol s)), ((d ⬝ᵥ y : ℝ) : EReal)

end BudgetedAffine.Disjoint


