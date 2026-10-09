-- Prove2me | Definitions.Def_OnlineCRS_Matroid_Basics
-- name    : OnlineCRS_Matroid_Basics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T19:21:06.811453+00:00
-- url     : https://prove2.me/theorems/dc4d1692-6f75-4e90-8274-563a05da66f8
-- title:
--   Definitions 1.3–1.5 — random active sets, greedy families and selectability
-- statement:
--   Let $N$ be a finite ground set. For a vector $x\in[0,1]^N$, the **active set** $R(x)$ contains each element $e$ independently with probability $x_e$. Thus a set $A\subseteq N$ has probability
--   $$\Pr[R(x)=A]=\prod_{e\in A}x_e\prod_{e\notin A}(1-x_e).$$
--
--   A **greedy family** $\mathcal F_x$ is a down-closed family of feasible sets containing the empty set. An element $e$ is **selectable** for $A$ when $I\cup\{e\}\in\mathcal F_x$ for every $I\subseteq A$ already in $\mathcal F_x$. A deterministic greedy OCRS assigns one such family to each $x$; it is $(b,c)$-selectable for a polytope $P$ when the selectability event has probability at least $c$ for every $x\in bP$ and every $e$. The randomized version uses an independent probability distribution over greedy families.
--
--   These definitions make the guarantee robust to any arrival order, including one chosen after all active elements are known. Requiring the empty set in every greedy family excludes a vacuous empty-family interpretation.
--
--   **Formalization Note** The probability formula is a probability when $0\le x_e\le1$ for every $e$. The predicates are total on real vectors; consuming theorems supply a polytope in $[0,1]^N$ and the paper's ranges $b,c\in[0,1]$. Lean requires a greedy family also for vectors outside that polytope, extending the algorithm's domain.
-- source:
--   arXiv:1508.00142v2, §1.1 and Definitions 1.3–1.5, pp. 2–4

import Mathlib

namespace OnlineCRS.Matroid

open scoped Pointwise

/-- `Pr[R(x) = A]` (arXiv:1508.00142v2, §1, p. 2): the random set `R(x)` contains every element `e`
independently with probability `x e`. The weights are those of the multilinear extension
`NonmonotoneSubmod.Shared.F`; they form a probability distribution on `Finset α` when `0 ≤ x ≤ 1`. -/
noncomputable def activeProb {α : Type} [Fintype α] [DecidableEq α] (x : α → ℝ) (A : Finset α) : ℝ :=
  ∏ e : α, if e ∈ A then x e else 1 - x e

/-- Definition 1.3 (p. 3), the family `F_x` of a greedy OCRS: a down-closed subfamily of the feasible sets
`𝓕`, containing `∅` (tacit in the paper; without it the empty family would be vacuously selectable). -/
def IsGreedyFamily {α : Type} (𝓕 : Finset α → Prop) (Fam : Finset (Finset α)) : Prop :=
  ∅ ∈ Fam ∧ (∀ I ∈ Fam, ∀ J : Finset α, J ⊆ I → J ∈ Fam) ∧ ∀ I ∈ Fam, 𝓕 I

/-- Definition 1.4 (p. 3): `e` is selectable for the active set `A` and the family `Fam`, i.e.
`I ∪ {e} ∈ Fam` for all `I ⊆ A` with `I ∈ Fam`. -/
def Selectable {α : Type} [DecidableEq α] (Fam : Finset (Finset α)) (A : Finset α) (e : α) : Prop :=
  ∀ I : Finset α, I ⊆ A → I ∈ Fam → insert e I ∈ Fam

open Classical in
/-- `Pr[I ∪ {e} ∈ Fam ∀ I ⊆ R(x), I ∈ Fam]` for a fixed family `Fam` (Definition 1.4, p. 3). -/
noncomputable def selProb {α : Type} [Fintype α] [DecidableEq α] (x : α → ℝ)
    (Fam : Finset (Finset α)) (e : α) : ℝ :=
  ∑ A : Finset α, if Selectable Fam A e then activeProb x A else 0

/-- Definitions 1.3–1.5 (pp. 3–4), deterministic case: the map `fam : x ↦ F_x` is a deterministic greedy
OCRS for the feasible sets `𝓕`, and it is `(b, c)`-selectable for the polytope `P`: for every `x ∈ b·P` and
every `e`, `Pr[e is selectable] ≥ c`. -/
def IsSelectableDet {α : Type} [Fintype α] [DecidableEq α] (𝓕 : Finset α → Prop) (P : Set (α → ℝ))
    (b c : ℝ) (fam : (α → ℝ) → Finset (Finset α)) : Prop :=
  (∀ x, IsGreedyFamily 𝓕 (fam x)) ∧ ∀ x ∈ b • P, ∀ e : α, c ≤ selProb x (fam x) e

/-- Definition 1.3 (p. 3), randomized case: for every `x`, `w x` is a probability distribution on families,
supported on greedy families for `𝓕` (the random choice of `F_x`, independent of `R(x)`). -/
def IsRandGreedyOCRS {α : Type} [Fintype α] [DecidableEq α] (𝓕 : Finset α → Prop)
    (w : (α → ℝ) → Finset (Finset α) → ℝ) : Prop :=
  ∀ x, (∀ Fam, 0 ≤ w x Fam) ∧ (∑ Fam : Finset (Finset α), w x Fam) = 1 ∧
    ∀ Fam, w x Fam ≠ 0 → IsGreedyFamily 𝓕 Fam

/-- Definitions 1.4–1.5 (pp. 3–4), randomized case: the probability over `R(x)` and the random choice of
`F_x` that `e` is selectable is at least `c`, for every `x ∈ b·P` and every `e`. -/
def IsSelectableRand {α : Type} [Fintype α] [DecidableEq α] (𝓕 : Finset α → Prop) (P : Set (α → ℝ))
    (b c : ℝ) (w : (α → ℝ) → Finset (Finset α) → ℝ) : Prop :=
  IsRandGreedyOCRS 𝓕 w ∧
    ∀ x ∈ b • P, ∀ e : α, c ≤ ∑ Fam : Finset (Finset α), w x Fam * selProb x Fam e

end OnlineCRS.Matroid


