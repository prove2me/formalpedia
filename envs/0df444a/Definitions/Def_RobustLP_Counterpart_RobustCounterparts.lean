-- Prove2me | Definitions.Def_RobustLP_Counterpart_RobustCounterparts
-- name    : RobustLP_Counterpart_RobustCounterparts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:25:23.956596+00:00
-- url     : https://prove2.me/theorems/449fc5c2-4024-4092-9d32-a1387540463d
-- title:
--   Feasibility for the counterparts (∗), (IRC[$\epsilon,\delta$]) and (RC[$\epsilon,\delta,\Omega$])
-- statement:
--   Let an uncertain linear program be given as in `UncertainLP`, with uncertain-entry sets $J_i$ and tolerated right-hand sides $b_i^+ = b_i+\delta\max[1,|b_i|]$. Fix parameters $\epsilon$, $\delta$, $\Omega$. This file defines feasibility for three optimization problems of the paper, all with the objective $c^Tx$.
--
--   1. **Problem (∗)**: $x$ is feasible if $Ex=e$, $Ax\le b$, $\ell\le x\le u$ and
--   $$
--   \sum_j a_{ij}x_j + \epsilon\sum_{j\in J_i}|a_{ij}||x_j| \le b_i + \delta\max[1,|b_i|]\qquad\forall i.
--   $$
--   2. **Interval robust counterpart (IRC[ε, δ])**: $(x,y)$, $y\in\mathbb{R}^n$, is feasible if $Ex=e$, $Ax\le b$, $\ell\le x\le u$, $-y_j\le x_j\le y_j$ for all $j$, and
--   $$
--   \sum_j a_{ij}x_j + \epsilon\sum_{j\in J_i}|a_{ij}|\,y_j \le b_i + \delta\max[1,|b_i|]\qquad\forall i.
--   $$
--   3. **Robust counterpart (RC[ε, δ, Ω])**: $(x,y,z)$ with $y=(y_{ij})$, $z=(z_{ij})$ is feasible if $Ex=e$, $Ax\le b$, $\ell\le x\le u$, $-y_{ij}\le x_j - z_{ij}\le y_{ij}$ for all $i,j$, and
--   $$
--   \sum_j a_{ij}x_j + \epsilon\Big[\sum_{j\in J_i}|a_{ij}|\,y_{ij} + \Omega\sqrt{\sum_{j\in J_i}a_{ij}^2 z_{ij}^2}\Big] \le b_i + \delta\max[1,|b_i|]\qquad\forall i.
--   $$
--
--   Problem (∗) characterizes reliable solutions; (IRC) is its linear-programming reformulation; (RC) is the conic counterpart whose feasible solutions are almost reliable under random symmetric perturbations (Proposition 1).
--
--   **Formalization Note** Two misprints of the page are corrected: in (IRC) the page prints $a_{ij}x_i$ in the first sum (it is $a_{ij}x_j$), and in (RC) it prints $\sum_{j\in J}$ in the first bracketed sum (it is $\sum_{j\in J_i}$). The constraint $-y_{ij}\le x_j-z_{ij}\le y_{ij}$ is kept for all pairs $(i,j)$ as printed. The square root is `Real.sqrt` of a sum of squares, hence of a nonnegative number.
-- source:
--   Ben-Tal and Nemirovski, Robust solutions of Linear Programming problems contaminated with uncertain data, Math. Program. Ser. A 88 (2000) 411–424, p. 417, §3.1, (∗); p. 418, §3.1, (IRC[ϵ, δ]) and (RC[ϵ, δ, Ω]) in Proposition 1

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP

namespace RobustLP.Counterpart

namespace UncertainLP

variable {n p m : ℕ}

/-- Feasibility for problem (∗) (Ben-Tal–Nemirovski 2000, §3.1, p. 417):
`E x = e`, `A x ≤ b`, `∑_j a_{ij} x_j + ε ∑_{j ∈ J_i} |a_{ij}| |x_j| ≤ b_i + δ max[1, |b_i|]` for all `i`,
and `ℓ ≤ x ≤ u`. -/
def StarFeasible (L : UncertainLP n p m) (ε δ : ℝ) (x : Fin n → ℝ) : Prop :=
  L.E.mulVec x = L.e ∧ L.A.mulVec x ≤ L.b ∧
    (∀ i : Fin m, ∑ j, L.A i j * x j + ε * ∑ j ∈ L.J i, |L.A i j| * |x j| ≤ L.bPlus δ i) ∧
    L.InBox x

/-- Feasibility of `(x, y)` for the interval robust counterpart (IRC[ε, δ])
(§3.1, p. 418): `E x = e`, `A x ≤ b`,
`∑_j a_{ij} x_j + ε ∑_{j ∈ J_i} |a_{ij}| y_j ≤ b_i + δ max[1, |b_i|]` for all `i`,
`-y_j ≤ x_j ≤ y_j` for all `j`, and `ℓ ≤ x ≤ u`. -/
def IRCFeasible (L : UncertainLP n p m) (ε δ : ℝ) (x y : Fin n → ℝ) : Prop :=
  L.E.mulVec x = L.e ∧ L.A.mulVec x ≤ L.b ∧
    (∀ i : Fin m, ∑ j, L.A i j * x j + ε * ∑ j ∈ L.J i, |L.A i j| * y j ≤ L.bPlus δ i) ∧
    (∀ j, -y j ≤ x j ∧ x j ≤ y j) ∧
    L.InBox x

/-- Feasibility of `(x, y, z)` for the robust counterpart (RC[ε, δ, Ω]) (§3.1, p. 418,
statement of Proposition 1): `E x = e`, `A x ≤ b`,
`∑_j a_{ij} x_j + ε [∑_{j ∈ J_i} |a_{ij}| y_{ij} + Ω √(∑_{j ∈ J_i} a_{ij}² z_{ij}²)] ≤ b_i + δ max[1, |b_i|]`
for all `i`, `ℓ ≤ x ≤ u`, and `-y_{ij} ≤ x_j - z_{ij} ≤ y_{ij}` for all `i, j`. -/
def RCFeasible (L : UncertainLP n p m) (ε δ Ω : ℝ) (x : Fin n → ℝ)
    (y z : Fin m → Fin n → ℝ) : Prop :=
  L.E.mulVec x = L.e ∧ L.A.mulVec x ≤ L.b ∧
    (∀ i : Fin m, ∑ j, L.A i j * x j +
        ε * (∑ j ∈ L.J i, |L.A i j| * y i j +
          Ω * Real.sqrt (∑ j ∈ L.J i, L.A i j ^ 2 * z i j ^ 2)) ≤ L.bPlus δ i) ∧
    L.InBox x ∧
    (∀ i j, -y i j ≤ x j - z i j ∧ x j - z i j ≤ y i j)

end UncertainLP

end RobustLP.Counterpart


