-- Prove2me | Definitions.Def_MurtyKabadi_Reduction_Construction
-- name    : MurtyKabadi_Reduction_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:13:05.988575+00:00
-- url     : https://prove2.me/theorems/27b090d0-2903-4695-9f6d-f16fc9a92faa
-- title:
--   The functions $f_1, f_2, f_4, f_5$, the polytope $P$ and the matrix $M$ of $f_5$ (pp. 123–124)
-- statement:
--   Fix subset sum data $d_0; d_1, \dots, d_n$, a positive integer $\delta$ and a positive rational $\varepsilon$. For $y, s \in \mathbb R^n$ (all sums over $j = 1, \dots, n$):
--   $$f_1(y,s) = \Big(\sum d_j y_j - d_0\Big)^2 + \delta \sum (y_j + s_j - 1)^2 + \sum y_j s_j,$$
--   $$f_2(y,s) = f_1(y,s) + 2 d_0 \sum d_j y_j (1 - y_j),$$
--   $$f_4(y,s) = \Big(\sum d_j y_j\Big)^2 + \delta \sum (y_j + s_j)^2 + \sum y_j s_j - 2 d_0 \sum d_j y_j^2 + \frac{d_0^2 - n\delta}{n^2}\Big(\sum (y_j + s_j)\Big)^2,$$
--   $$f_5(y,s) = f_4(y,s) - \frac{\varepsilon}{n^2}\Big(\sum (y_j + s_j)\Big)^2,$$
--   and the polytope
--   $$P = \Big\{(y,s) : y \ge 0,\ s \ge 0,\ \sum (y_j + s_j) = n\Big\}.$$
--   The function $f_5$ is a quadratic form in the $2n$ variables $(y, s)$. Its symmetric matrix $M$, indexed by the $y$-coordinates and then the $s$-coordinates, is given entrywise, with $c = (d_0^2 - n\delta - \varepsilon)/n^2$, by
--   $$M_{y_i y_j} = d_i d_j + c + [i=j](\delta - 2 d_0 d_j),\qquad M_{y_i s_j} = M_{s_j y_i} = c + [i=j](\delta + \tfrac12),\qquad M_{s_i s_j} = c + [i=j]\,\delta.$$
--   The paper's $f_3$ is not needed and is not defined.
--
--   These objects are the reduction from subset sum to the quadratic problems: Problems 6–9 ask for points of $P$ where $f_1, f_2, f_4 \le 0$ or $f_5 < 0$, and the matrix $M$ is the output of the reduction.
--
--   **Formalization Note** $d, d_0, \delta$ are natural numbers and $\varepsilon$ is rational, all cast to $\mathbb R$. The pair $(y,s)$ is the argument `Sum.elim y s` of $M$ on the index type `Fin n ⊕ Fin n`. The entries of $M$ are written out explicitly (not "some matrix with quadratic form $f_5$"); the identity $f_5(y,s) = x^{\mathsf T} M x$ is a milestone. For $n = 0$ Lean's convention $a/0 = 0$ makes the $n^2$ coefficients $0$; this case is harmless for the goal and is excluded by `0 < n` where it matters.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), pp. 123–124, definitions of f1, f2, f4, f5 and P; the matrix M is the coefficient matrix of f5 (p. 124)

import Mathlib

namespace MurtyKabadi.Reduction

/-- `f₁(y, s)` (p. 123). -/
noncomputable def f1 {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (y s : Fin n → ℝ) : ℝ :=
  (∑ j, (d j : ℝ) * y j - d0) ^ 2 + (δ : ℝ) * (∑ j, (y j + s j - 1) ^ 2) + ∑ j, y j * s j

/-- `f₂(y, s) = f₁(y, s) + 2 d₀ ∑ d_j y_j (1 − y_j)` (p. 123). -/
noncomputable def f2 {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (y s : Fin n → ℝ) : ℝ :=
  f1 d d0 δ y s + 2 * (d0 : ℝ) * ∑ j, (d j : ℝ) * y j * (1 - y j)

/-- `f₄(y, s)` (p. 124). -/
noncomputable def f4 {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (y s : Fin n → ℝ) : ℝ :=
  (∑ j, (d j : ℝ) * y j) ^ 2 + (δ : ℝ) * ∑ j, (y j + s j) ^ 2 + ∑ j, y j * s j
    - 2 * (d0 : ℝ) * ∑ j, (d j : ℝ) * y j ^ 2
    + (((d0 : ℝ) ^ 2 - n * δ) / (n : ℝ) ^ 2) * (∑ j, (y j + s j)) ^ 2

/-- `f₅(y, s) = f₄(y, s) − (ε / n²) (∑ (y_j + s_j))²` (p. 124). -/
noncomputable def f5 {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (ε : ℚ) (y s : Fin n → ℝ) : ℝ :=
  f4 d d0 δ y s - ((ε : ℝ) / (n : ℝ) ^ 2) * (∑ j, (y j + s j)) ^ 2

/-- The polytope `P = {(y, s) : y ≥ 0, s ≥ 0, ∑ (y_j + s_j) = n}` (p. 124). -/
def P (n : ℕ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ ∑ j, (p.1 j + p.2 j) = n}

/-- The symmetric matrix of the quadratic form `f₅` on the variables `(y, s)`, indexed by
`Fin n ⊕ Fin n` (`Sum.inl j ↔ y_j`, `Sum.inr j ↔ s_j`). With `c = (d₀² − nδ − ε)/n²`:
`(y_i, y_j)` entry `d_i d_j + c` (plus `δ − 2 d₀ d_j` if `i = j`); `(y_i, s_j)` and `(s_j, y_i)`
entries `c` (plus `δ + 1/2` if `i = j`); `(s_i, s_j)` entry `c` (plus `δ` if `i = j`). -/
noncomputable def mkMatrix {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (ε : ℚ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  let c : ℝ := ((d0 : ℝ) ^ 2 - n * δ - ε) / (n : ℝ) ^ 2
  fun a b =>
    match a, b with
    | Sum.inl i, Sum.inl j =>
        (d i : ℝ) * d j + c + if i = j then (δ : ℝ) - 2 * d0 * d j else 0
    | Sum.inl i, Sum.inr j => c + if i = j then (δ : ℝ) + 1 / 2 else 0
    | Sum.inr i, Sum.inl j => c + if i = j then (δ : ℝ) + 1 / 2 else 0
    | Sum.inr i, Sum.inr j => c + if i = j then (δ : ℝ) else 0

end MurtyKabadi.Reduction


