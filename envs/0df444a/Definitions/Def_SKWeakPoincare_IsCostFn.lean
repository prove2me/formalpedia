-- Prove2me | Definitions.Def_SKWeakPoincare_IsCostFn
-- name    : SKWeakPoincare_IsCostFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:09.041441+00:00
-- url     : https://prove2.me/theorems/04a4004e-ff46-42c4-a043-ecc1a5529de2
-- title:
--   Cost functions $\mathfrak e:[0,T]\times\mathbb R^n\to[0,4n]$ and the Lipschitz property with cost functions
-- statement:
--   A **cost function** is a jointly Borel function $\mathfrak e:[0,T]\times\mathbb R^n\to[0,4n]$. A map $m:\mathbb R^n\to\mathbb R^n$ has the **Lipschitz property with cost functions** with constant $L$ if, for every $t\in[0,T]$ and all $y_1,y_2\in\mathbb R^n$,
--   $$
--   \|m(y_1)-m(y_2)\|_2\le L\|y_1-y_2\|_2+\sqrt{\mathfrak e(t;y_1)}+\sqrt{\mathfrak e(t;y_2)}.
--   $$
--
--   This replaces a global Lipschitz bound on the posterior mean, which is not available for the SK model, by a Lipschitz bound up to a cost that is small along typical localization paths (Lemmas 2.1 and 6.1).
--
--   **Formalization Note** $\mathfrak e$ is a Borel function on all of $\mathbb R\times\mathbb R^n$, and only its values on $[0,T]\times\mathbb R^n$ are constrained. Every Borel function on $[0,T]\times\mathbb R^n$ extends to one on $\mathbb R\times\mathbb R^n$. Norms are Euclidean.
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Lemma 2.1, p.8 (cost functions, property (i)); Lemma 6.1, p.37

import Mathlib

namespace SKWeakPoincare

/-- `𝔢` is a **cost function** on `[0, T] × ℝ^n`: jointly Borel, with values in `[0, 4n]`.
Hou–Liu–Yu, arXiv:2610.09882, Lemma 6.1, p. 37 ("a jointly Borel function
`𝔢 : [0, T] × ℝ^n → [0, 4n]`"), and Lemma 2.1, p. 8 (for fixed `A`).

**Formalization Note.** `𝔢` is a function on all of `ℝ × ℝ^n`, Borel there, and only its values on
`[0, T] × ℝ^n` are constrained (every Borel function on `[0, T] × ℝ^n` extends to one on
`ℝ × ℝ^n`). `ℝ^n` is `EuclideanSpace ℝ (Fin n)`. -/
def IsCostFn (T : ℝ) (n : ℕ) (e : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Measurable (Function.uncurry e) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y, 0 ≤ e t y ∧ e t y ≤ 4 * (n : ℝ)

/-- **Lipschitz property with cost functions** of a map `m : ℝ^n → ℝ^n`: for every `t ∈ [0, T]` and
`y₁, y₂ ∈ ℝ^n`, `‖m(y₁) − m(y₂)‖₂ ≤ L ‖y₁ − y₂‖₂ + √𝔢(t; y₁) + √𝔢(t; y₂)`.
Hou–Liu–Yu, arXiv:2610.09882, Lemma 2.1 (i), p. 8, and Lemma 6.1, p. 37.

**Formalization Note.** Norms are the Euclidean norms of `EuclideanSpace ℝ (Fin n)`. -/
def HasLipCost {n : ℕ} (T L : ℝ) (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (e : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y₁ y₂,
    ‖m y₁ - m y₂‖ ≤ L * ‖y₁ - y₂‖ + Real.sqrt (e t y₁) + Real.sqrt (e t y₂)

end SKWeakPoincare


