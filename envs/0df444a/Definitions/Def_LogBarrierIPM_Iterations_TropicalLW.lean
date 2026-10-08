-- Prove2me | Definitions.Def_LogBarrierIPM_Iterations_TropicalLW
-- name    : LogBarrierIPM_Iterations_TropicalLW
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T13:45:53.454106+00:00
-- url     : https://prove2.me/theorems/4ee52920-9ad9-4b79-88dc-9bdc1be7fdf8
-- title:
--   The tropical polyhedron (26) of $\mathbf{LW}_r$ and the recursion $x^\lambda$ of Proposition 20
-- statement:
--   Fix $r\ge1$. The tropical polyhedron $\mathcal P'\subseteq\mathbb T^{2r}$ is given by the $3r-1$ tropical inequalities (26):
--   $$x_1\le2,\qquad x_2\le1,$$
--   $$x_{2j+1}\le1+x_{2j-1},\quad x_{2j+1}\le1+x_{2j},\quad x_{2j+2}\le(1-1/2^j)+\max(x_{2j-1},x_{2j})\qquad(1\le j<r),$$
--   with $\mathbb T=\mathbb R\cup\{-\infty\}$. For $\lambda\in\mathbb R$, the point $x^\lambda\in\mathbb R^{2r}$ is given by the recursion
--   $$x^\lambda_1=\min(\lambda,2),\qquad x^\lambda_2=1,$$
--   $$x^\lambda_{2j+1}=1+\min(x^\lambda_{2j-1},x^\lambda_{2j}),\qquad x^\lambda_{2j+2}=(1-1/2^j)+\max(x^\lambda_{2j-1},x^\lambda_{2j})\qquad(1\le j<r).$$
--
--   The paper claims (p. 18–19) that $\mathcal P'$ is the image under the valuation of the feasible set of $\mathrm{LW}_r$ over Puiseux series, and Proposition 20 shows that $x^\lambda$ is the barycenter of $\{x\in\mathcal P' : x_1\le\lambda\}$, i.e. the $x$-part of the primal tropical central path of $\mathrm{LW}_r$; the recursion makes that curve explicit. Neither fact is part of this definition: $\mathcal P'$ is defined as the set cut out by (26), and $x^\lambda$ as the recursion.
--
--   **Formalization Note** $\mathbb T$ is `WithBot ℝ`, so $a+(-\infty)=-\infty$ as in the tropical semiring. The page announces "$3r+1$ tropical linear inequalities" but displays the $3r-1$ above; the remaining two are the tropicalized non-negativity constraints $x_{2r-1},x_{2r}\ge0$ of $\mathrm{LW}_r$, which hold for every point of $\mathbb T^{2r}$ and are therefore omitted. Points of $\mathbb T^{2r}$ have 0-based Lean indices; the inequalities are written through an accessor that takes the paper's 1-based index $k\in[1,2r]$ (and is not used outside that range). The recursion is computed in pairs $(x^\lambda_{2j+1},x^\lambda_{2j+2})$, $j\ge0$. The definition is meant for $r\ge1$, as in the paper; every theorem that uses it assumes $1\le r$.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 19, eq. (26) and Proposition 20

import Mathlib

namespace LogBarrierIPM.Iterations

/-- The pairs `(x^λ_{2j+1}, x^λ_{2j+2})`, `j ≥ 0`, of the recursion of Proposition 20 (p. 19):
`(x^λ_1, x^λ_2) = (min(λ, 2), 1)` and, for `j ≥ 1`,
`x^λ_{2j+1} = 1 + min(x^λ_{2j−1}, x^λ_{2j})`,
`x^λ_{2j+2} = (1 − 1/2^j) + max(x^λ_{2j−1}, x^λ_{2j})`. -/
noncomputable def xPair (lam : ℝ) : ℕ → ℝ × ℝ
  | 0 => (min lam 2, 1)
  | j + 1 =>
    (1 + min (xPair lam j).1 (xPair lam j).2,
      (1 - 1 / 2 ^ (j + 1)) + max (xPair lam j).1 (xPair lam j).2)

/-- The point `x^λ ∈ ℝ^{2r}` given by the recursion of Proposition 20; the 0-based Lean index
`k` is the paper's `x_{k+1}`. -/
noncomputable def xLam (r : ℕ) (lam : ℝ) : Fin (2 * r) → ℝ :=
  fun k => if k.val % 2 = 0 then (xPair lam (k.val / 2)).1 else (xPair lam (k.val / 2)).2

/-- The paper's 1-based coordinate `x_k` of `x ∈ 𝕋^{2r}` (`−∞` outside `1 ≤ k ≤ 2r`; only used
inside that range). -/
def coord {r : ℕ} (x : Fin (2 * r) → WithBot ℝ) (k : ℕ) : WithBot ℝ :=
  if h : 1 ≤ k ∧ k ≤ 2 * r then x ⟨k - 1, by omega⟩ else ⊥

/-- The tropical polyhedron `𝒫' ⊆ 𝕋^{2r}` given by the `3r − 1` tropical inequalities (26)
(p. 19): `x_1 ≤ 2`, `x_2 ≤ 1`, and for `1 ≤ j < r`: `x_{2j+1} ≤ 1 + x_{2j−1}`,
`x_{2j+1} ≤ 1 + x_{2j}`, `x_{2j+2} ≤ (1 − 1/2^j) + max(x_{2j−1}, x_{2j})`
(`𝕋 = ℝ ∪ {−∞}` as `WithBot ℝ`). -/
def tropicalLWSet (r : ℕ) : Set (Fin (2 * r) → WithBot ℝ) :=
  {x | coord x 1 ≤ ((2 : ℝ) : WithBot ℝ) ∧ coord x 2 ≤ ((1 : ℝ) : WithBot ℝ) ∧
    ∀ j : ℕ, 1 ≤ j → j < r →
      coord x (2 * j + 1) ≤ ((1 : ℝ) : WithBot ℝ) + coord x (2 * j - 1) ∧
      coord x (2 * j + 1) ≤ ((1 : ℝ) : WithBot ℝ) + coord x (2 * j) ∧
      coord x (2 * j + 2) ≤
        ((1 - 1 / 2 ^ j : ℝ) : WithBot ℝ) + max (coord x (2 * j - 1)) (coord x (2 * j))}

end LogBarrierIPM.Iterations


