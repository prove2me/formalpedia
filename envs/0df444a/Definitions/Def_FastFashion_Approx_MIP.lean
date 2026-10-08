-- Prove2me | Definitions.Def_FastFashion_Approx_MIP
-- name    : FastFashion_Approx_MIP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:59.639281+00:00
-- url     : https://prove2.me/theorems/ebe46236-4912-4bcd-80b7-6c9857c4bfe5
-- title:
--   §3.2: the shipment program (MIP), constraints (13)–(19), feasibility and optimality
-- statement:
--   This file states the mixed integer program (MIP) of Caro and Gallien (§3.2) for distributing warehouse inventory to a finite set of stores $J$.
--
--   **Data.** Sizes $\mathcal S = \mathcal S^+ \cup \mathcal S^-$ as before; for each store $j$ a unit selling price $P_j$; an exogenous unit value $K$ of inventory left in the warehouse; warehouse inventory $W_s \in \mathbb N$; store inventory $I_{sj} \in \mathbb N$; demand rates $\lambda_{sj}$; the period $T$; and tangent index sets $\mathcal N(\lambda_{sj}) \subseteq \mathbb N \cup \{\infty\}$ with the coefficients $a_i, b_i$ of (6).
--
--   **Variables.** Shipments $x_{sj}$, approximate expected sales $z_j$, and auxiliary variables $y_j$ and $v_{sj}$.
--
--   **Program.**
--   $$\max \ \sum_{j\in J} P_j z_j + K\Big(\sum_{s\in\mathcal S}\big(W_s - \sum_{j\in J} x_{sj}\big)\Big) \qquad (13)$$
--   subject to
--   1. $\sum_{j\in J} x_{sj} \le W_s$ for all $s \in \mathcal S$; (14)
--   2. $z_j \le \big(\sum_{s\in\mathcal S^+}\lambda_{sj}\big) y_j + \sum_{s \in \mathcal S^-}\lambda_{sj} v_{sj}$ for all $j$; (15)
--   3. $y_j \le a_i(\lambda_{sj})(I_{sj} + x_{sj} - i) + b_i(\lambda_{sj})$ for all $j$, $s\in\mathcal S^+$, $i \in \mathcal N(\lambda_{sj})$; (16)
--   4. $v_{sj} \le a_i(\lambda_{sj})(I_{sj} + x_{sj} - i) + b_i(\lambda_{sj})$ for all $j$, $s\in\mathcal S^-$, $i \in \mathcal N(\lambda_{sj})$; (17)
--   5. $v_{sj} \le y_j$ for all $j$, $s \in \mathcal S^-$; (18)
--   6. $z_j, y_j \ge 0$ for all $j$; $v_{sj} \ge 0$ for $(s,j) \in \mathcal S^- \times J$; $x_{sj} \in \mathbb N$. (19)
--
--   A solution is **feasible** if it satisfies (14)–(19), and **optimal** if it is feasible and its objective (13) is at least that of every feasible solution.
--
--   **Formalization Note** For $i = \infty$ the right-hand side of (16)–(17) is the constant $T$ (the paper's $a_\infty = 0$, $b_\infty = T$). The slopes $a_i$ are the index-corrected ones of the definition file `FastFashion.Approx.Tangents`. Integrality of $x_{sj}$ is carried by its type $\mathbb N$; (14) is compared in $\mathbb N$ and (13) is computed in $\mathbb R$. The variables $v_{sj}$ for major sizes $s$ appear in no constraint and in the objective of no solution; they are left free. No existence of an optimal solution is asserted.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 15, §3.2, (MIP) (13)–(19); p. 13 (P_j); p. 16 (K, x_j, I_j, λ_j)

import Mathlib
import Definitions.Def_FastFashion_Approx_Tangents

namespace FastFashion.Approx

/-- A candidate solution of (MIP) (§3.2, p. 15): shipments `x s j ∈ ℕ` of size `s` to store `j`,
approximate expected sales `z j`, and the auxiliary variables `y j` and `v s j`. -/
structure MIPSol (S J : Type*) where
  x : S → J → ℕ
  z : J → ℝ
  y : J → ℝ
  v : S → J → ℝ

/-- The objective (13) of (MIP): `∑_{j ∈ J} P_j z_j + K (∑_{s ∈ S} (W_s − ∑_{j ∈ J} x_{sj}))`. -/
noncomputable def mipObjective {S J : Type*} [Fintype S] [Fintype J] (P : J → ℝ) (K : ℝ)
    (W : S → ℕ) (sol : MIPSol S J) : ℝ :=
  ∑ j, P j * sol.z j + K * ∑ s, ((W s : ℝ) - ∑ j, (sol.x s j : ℝ))

/-- Feasibility for (MIP), constraints (14)–(19) (p. 15), with rates `lam s j = λ_{sj}`, period
`T`, major sizes `Sp` (minor sizes `Spᶜ`), tangent index sets `Nset s j = 𝒩(λ_{sj})`, warehouse
stock `W` and store stock `I`. The tangent `a_i(λ)(I + x − i) + b_i(λ)` is `tangent λ T i (I + x)`
(the constant `T` for `i = ∞`). Integrality `x s j ∈ ℕ` of (19) is carried by the type. -/
def MIPFeasible {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] (lam : S → J → ℝ) (T : ℝ)
    (Sp : Finset S) (Nset : S → J → Finset (WithTop ℕ)) (W : S → ℕ) (I : S → J → ℕ)
    (sol : MIPSol S J) : Prop :=
  -- (14)
  (∀ s, ∑ j, sol.x s j ≤ W s) ∧
  -- (15)
  (∀ j, sol.z j ≤ (∑ s ∈ Sp, lam s j) * sol.y j + ∑ s ∈ Spᶜ, lam s j * sol.v s j) ∧
  -- (16)
  (∀ j, ∀ s ∈ Sp, ∀ i ∈ Nset s j,
    sol.y j ≤ tangent (lam s j) T i ((I s j : ℝ) + (sol.x s j : ℝ))) ∧
  -- (17)
  (∀ j, ∀ s ∈ Spᶜ, ∀ i ∈ Nset s j,
    sol.v s j ≤ tangent (lam s j) T i ((I s j : ℝ) + (sol.x s j : ℝ))) ∧
  -- (18)
  (∀ j, ∀ s ∈ Spᶜ, sol.v s j ≤ sol.y j) ∧
  -- (19)
  (∀ j, 0 ≤ sol.z j ∧ 0 ≤ sol.y j) ∧ (∀ j, ∀ s ∈ Spᶜ, 0 ≤ sol.v s j)

/-- An optimal solution of (MIP): feasible, with objective (13) at least that of every feasible
solution. -/
def MIPOptimal {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] (P : J → ℝ) (K : ℝ)
    (lam : S → J → ℝ) (T : ℝ) (Sp : Finset S) (Nset : S → J → Finset (WithTop ℕ)) (W : S → ℕ)
    (I : S → J → ℕ) (sol : MIPSol S J) : Prop :=
  MIPFeasible lam T Sp Nset W I sol ∧
    ∀ sol' : MIPSol S J, MIPFeasible lam T Sp Nset W I sol' →
      mipObjective P K W sol' ≤ mipObjective P K W sol

end FastFashion.Approx


