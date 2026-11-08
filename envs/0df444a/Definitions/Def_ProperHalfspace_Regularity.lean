-- Prove2me | Definitions.Def_ProperHalfspace_Regularity
-- name    : ProperHalfspace_Regularity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:52.687908+00:00
-- url     : https://prove2.me/theorems/5024207a-4e90-4d20-9f50-dc4377762f07
-- title:
--   Regularity, the critical index, and $\Lambda_\nu$
-- statement:
--   For $\tau>0$, the zero vector is $\tau$-regular, and a nonzero vector $w$ is $\tau$-regular if $\|w\|_\infty\le\tau\|w\|_2$. For $\tau\in(0,1)$ and $w\in\mathbb R^m$ with $|w_1|\ge\dots\ge|w_m|$, the $\tau$-critical index is the least $k\in\{0,\dots,m\}$ with
--   $$\max_{j>k}|w_j|\le\tau\Bigl(\sum_{j>k}w_j^2\Bigr)^{1/2},$$
--   the maximum over an empty set being $0$. For $\nu\in(0,1/2)$, $\Lambda_\nu=\log(e+\log(1/\nu))$.
--
--   **Formalization Note** Regularity is generic in the finite index type, because the paper applies it to vectors in $\mathbb R^{H^c}$. With 0-based coordinates, the tail after the first $k$ coordinates is $\{j:k\le j\}$. The critical index is the least element of a subset of $\{0,\dots,m\}$ that contains $m$, so the natural-number infimum is never of an empty set.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Definition 6, p.14; Definition 8 and the display after it, p.16

import Mathlib

namespace ProperHalfspace

/-!
# Regularity and the critical index

De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026), Definition 6, p.14; Definition 8, p.16.

**Formalization Note.** `IsRegular` is generic in the index type, because the paper applies it to vectors in `ℝ^{Hᶜ}`. The
critical index uses 0-based coordinates: the tail after the first `k` coordinates is `{j : Fin m | k ≤ j}`, the page's
`j > k`. The page's `max` over an empty tail is `0`, which is what the `∀ j` form gives. The critical index is the least
element of a subset of `{0, …, m}` containing `m`, so the `ℕ` infimum is never taken over the empty set.
-/

/-- Definition 6: the zero vector is `τ`-regular, and a nonzero `w` is `τ`-regular iff `‖w‖_∞ ≤ τ ‖w‖₂`. -/
def IsRegular {ι : Type*} [Fintype ι] (τ : ℝ) (w : ι → ℝ) : Prop :=
  w = 0 ∨ ∀ i, |w i| ≤ τ * Real.sqrt (∑ j, w j ^ 2)

/-- The defining inequality of Definition 8 at `k`: `max_{j>k} |w_j| ≤ τ (Σ_{j>k} w_j²)^{1/2}`. -/
def TailRegularAt {m : ℕ} (τ : ℝ) (w : Fin m → ℝ) (k : ℕ) : Prop :=
  ∀ j : Fin m, k ≤ (j : ℕ) →
    |w j| ≤ τ * Real.sqrt (∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ (i : ℕ)), w i ^ 2)

/-- Definition 8: the `τ`-critical index, the least `k ∈ {0, …, m}` with `TailRegularAt τ w k`. -/
noncomputable def criticalIndex {m : ℕ} (τ : ℝ) (w : Fin m → ℝ) : ℕ :=
  sInf {k : ℕ | k ≤ m ∧ TailRegularAt τ w k}

/-- `Λ_ν = log(e + log(1/ν))` (p.16). -/
noncomputable def lam (ν : ℝ) : ℝ := Real.log (Real.exp 1 + Real.log (1 / ν))

end ProperHalfspace


