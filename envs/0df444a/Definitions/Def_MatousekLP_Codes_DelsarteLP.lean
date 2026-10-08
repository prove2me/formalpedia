-- Prove2me | Definitions.Def_MatousekLP_Codes_DelsarteLP
-- name    : MatousekLP_Codes_DelsarteLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T13:02:10.326975+00:00
-- url     : https://prove2.me/theorems/7f12fc5a-b18b-4fb8-ae23-0666e50bc2d8
-- title:
--   Theorem 8.4.3 — Krawtchouk numbers $K_t(n,i)$, the quantities $\tilde x_i(C)$, and the Delsarte linear program
-- statement:
--   For integers $0 \le i, t \le n$ the **Krawtchouk number** is
--   $$
--   K_t(n,i) = \sum_{j=0}^{\min(i,t)} (-1)^j \binom{i}{j}\binom{n-i}{t-j}.
--   $$
--
--   For a code $C \subseteq \{0,1\}^n$ and $i = 0,\dots,n$ put
--   $$
--   \tilde x_i(C) = \frac{1}{|C|}\,\bigl|\{(\mathbf w,\mathbf w') \in C^2 : d_H(\mathbf w,\mathbf w') = i\}\bigr|,
--   $$
--   the number of ordered pairs of code words at Hamming distance $i$, divided by the number of code words.
--
--   The **Delsarte linear program** for parameters $n, d$ has variables $x_0,\dots,x_n$:
--   $$
--   \begin{aligned}
--   \text{maximize}\quad & x_0 + x_1 + \dots + x_n\\
--   \text{subject to}\quad & x_0 = 1,\\
--   & x_i = 0, \quad i = 1,\dots,d-1,\\
--   & \textstyle\sum_{i=0}^n K_t(n,i)\, x_i \ge 0, \quad t = 1,\dots,n,\\
--   & x_0,\dots,x_n \ge 0.
--   \end{aligned}
--   $$
--   This file defines $K_t(n,i)$, $\tilde x_i(C)$, the feasibility predicate of this program and its objective.
--
--   **Formalization Note** $K_t(n,i)$ is an integer; the subtractions $n-i$ and $t-j$ are natural-number subtractions, honest in the book's range $i \le n$, $j \le t$. The variables $x_0,\dots,x_n$ are a vector indexed by `Fin (n+1)` with $x_i$ = `x i` (no index shift). The constraint "$x_i = 0$ for $i = 1,\dots,d-1$" is written $1 \le i < d$, so it is vacuous for $d \le 1$ and covers all $i \ge 1$ when $d > n$. For the empty code Lean's convention $1/0 = 0$ gives $\tilde x_i(\emptyset) = 0$; the book only uses $\tilde x$ for codes with at least one word.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, pp. 159–160, Theorem 8.4.3 (K_t(n,i) and the linear program), p. 160 (definition of x̃_i)

import Mathlib
import Definitions.Def_MatousekLP_Codes_Basic

open Finset

namespace MatousekLP.Codes

/-- The Krawtchouk number of Theorem 8.4.3 (p. 159): for integers `0 ≤ i, t ≤ n`,
`K_t(n, i) = ∑_{j=0}^{min(i,t)} (-1)^j (i choose j) (n-i choose t-j)`.
The natural-number subtractions `n - i` and `t - j` are honest in the book's range
`i ≤ n`, `j ≤ t`. -/
def K (n t i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (min i t + 1), (-1 : ℤ) ^ j * (i.choose j : ℤ) * ((n - i).choose (t - j) : ℤ)

/-- The quantity `x̃_i(C)` of p. 160: the number of ordered pairs `(w, w') ∈ C²` with
`d_H(w, w') = i`, divided by `|C|`. (For the empty code Lean's `1/0 = 0` makes it `0`.) -/
noncomputable def xtilde {n : ℕ} (C : Finset (Word n)) (i : ℕ) : ℝ :=
  (1 / (C.card : ℝ)) * (#{p ∈ C ×ˢ C | hammingDist p.1 p.2 = i} : ℝ)

/-- Feasibility for the Delsarte linear program of Theorem 8.4.3 (p. 160), in the variables
`x_0, …, x_n` (indexed by `Fin (n+1)`, variable `x_i` is `x i`):
`x_0 = 1`; `x_i = 0` for `i = 1, …, d-1`; `∑_{i=0}^n K_t(n,i) x_i ≥ 0` for `t = 1, …, n`;
`x_0, …, x_n ≥ 0`. -/
def IsDelsarteFeasible (n d : ℕ) (x : Fin (n + 1) → ℝ) : Prop :=
  x 0 = 1 ∧
  (∀ i : Fin (n + 1), 1 ≤ (i : ℕ) → (i : ℕ) < d → x i = 0) ∧
  (∀ t : ℕ, 1 ≤ t → t ≤ n → 0 ≤ ∑ i : Fin (n + 1), (K n t i : ℝ) * x i) ∧
  (∀ i : Fin (n + 1), 0 ≤ x i)

/-- The objective `x_0 + x_1 + ⋯ + x_n` of the Delsarte linear program (p. 160). -/
def delsarteObjective {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ := ∑ i : Fin (n + 1), x i

end MatousekLP.Codes


