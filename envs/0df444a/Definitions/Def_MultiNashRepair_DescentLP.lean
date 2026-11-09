-- Prove2me | Definitions.Def_MultiNashRepair_DescentLP
-- name    : MultiNashRepair_DescentLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:29:18.697206+00:00
-- url     : https://prove2.me/theorems/e3771547-600f-4274-831c-2b6e86197069
-- title:
--   The linearized descent LP (3.1), its dual, and the dual law $\lambda$ with deviations $b_i$
-- statement:
--   Fix a mixed profile $x$ and a step size $\eta$. A direction $z=(z_{j,b})$ is **feasible** if $z\ge0$ and $\sum_{j,b}z_{j,b}\le1$. The **linearized descent LP** (3.1)/(5.9) is
--   $$z^\star=\min_{z\text{ feasible}}\ \max_{i,a}\Bigl[g_{i,a}(x)+\eta\sum_{j,b}z_{j,b}\,\Delta_{j,b}g_{i,a}(x)\Bigr].$$
--   It **passes** when $z^\star\le\mathrm{Reg}(x)-\eta\mu/m$ (Algorithm 1, line 9).
--
--   Its exact dual (p.18) maximizes $\sum_{i,a}w_{i,a}g_{i,a}(x)-\alpha$ over $w\ge0$ with $\sum_{i,a}w_{i,a}=1$, $\alpha\ge0$ and $\alpha+\eta\sum_{i,a}w_{i,a}\Delta_{j,b}g_{i,a}\ge0$ for every $(j,b)$; an optimal dual is a feasible one whose objective equals $z^\star$.
--
--   From $w$: the **player law** $\lambda_i=\sum_a w_{i,a}$, the **mixed deviations** $b_i=\sum_a w_{i,a}e_a/\lambda_i$ when $\lambda_i>0$ and $b_i=e_0$ (the smallest-indexed action) when $\lambda_i=0$ (3.4), and the **replacement columns**
--   $$F_j(y_j)=\sum_i\lambda_i\,d_{i,b_i}(x[j\leftarrow y_j]).$$
--
--   **Formalization Note** $z^\star$ is an infimum over the feasible polytope (attained). Optimal duals are defined by strong duality.
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), §3.1, (3.1), p.6; (3.4), p.8; §5.2, (5.9), p.17, and the dual, p.18; (4.4), p.12

import Mathlib
import Definitions.Def_MultiNashRepair_Regret

open NashAmplification.Filtering (Mixed Utility Tuple)
open Finset

noncomputable section

namespace MultiNashRepair

variable {m : ℕ} {n : Fin m → ℕ}

/-- **The linearized descent LP (3.1)/(5.9), its dual, and the dual's player law and
deviations** (Tang, Ding, Fang, arXiv:2611.06076, §3.1 pp.6–8 and §5.2 pp.17–18).

A direction is `z = (z_{j,b})`; it is feasible when `z ≥ 0` and `Σ_{j,b} z_{j,b} ≤ 1`. -/
def LPFeasible (z : (j : Fin m) → Fin (n j) → ℝ) : Prop :=
  (∀ j b, 0 ≤ z j b) ∧ ∑ j, ∑ b, z j b ≤ 1

/-- The objective of (5.9): `max_{i,a} [g_{i,a}(x) + η Σ_{j,b} z_{j,b} Δ_{j,b} g_{i,a}(x)]`, a
supremum over the finite set of pairs `(i, a)` (the maximum when `1 ≤ m` and every `n i > 0`). -/
def lpObj (u : Utility n) (x : Mixed n) (η : ℝ) (z : (j : Fin m) → Fin (n j) → ℝ) : ℝ :=
  ⨆ p : (Σ i : Fin m, Fin (n i)),
    (gain u x p.1 p.2 + η * ∑ j, ∑ b, z j b * repl u x j b p.1 p.2)

/-- The optimal value `z⋆` of the LP (3.1)/(5.9): the infimum of the objective over feasible
directions (attained: the feasible set is a nonempty polytope). -/
def lpValue (u : Utility n) (x : Mixed n) (η : ℝ) : ℝ :=
  sInf (lpObj u x η '' {z | LPFeasible z})

/-- An optimal solution of the LP. -/
def LPOptimal (u : Utility n) (x : Mixed n) (η : ℝ) (z : (j : Fin m) → Fin (n j) → ℝ) : Prop :=
  LPFeasible z ∧ lpObj u x η z = lpValue u x η

/-- The LP **passes** (succeeds) when its optimum is at most `Reg(x) − η µ/m` (Algorithm 1
line 9, p.7; §5.2, p.17). -/
def LPPasses (u : Utility n) (x : Mixed n) (η mu : ℝ) : Prop :=
  lpValue u x η ≤ Reg u x - η * mu / m

/-- Feasibility for the exact dual of (5.9) (p.18): `w ≥ 0`, `Σ_{i,a} w_{i,a} = 1`, `α ≥ 0`, and
`α + η Σ_{i,a} w_{i,a} Δ_{j,b} g_{i,a} ≥ 0` for every `(j, b)`. -/
def DualFeasible (u : Utility n) (x : Mixed n) (η : ℝ) (w : (i : Fin m) → Fin (n i) → ℝ)
    (α : ℝ) : Prop :=
  (∀ i a, 0 ≤ w i a) ∧ ∑ i, ∑ a, w i a = 1 ∧ 0 ≤ α ∧
    ∀ j (b : Fin (n j)), 0 ≤ α + η * ∑ i, ∑ a, w i a * repl u x j b i a

/-- The dual objective `Σ_{i,a} w_{i,a} g_{i,a}(x) − α` (p.18). -/
def dualObj (u : Utility n) (x : Mixed n) (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ) : ℝ :=
  ∑ i, ∑ a, w i a * gain u x i a - α

/-- An optimal dual solution: feasible, with objective equal to the LP's optimal value (strong
duality). -/
def DualOptimal (u : Utility n) (x : Mixed n) (η : ℝ) (w : (i : Fin m) → Fin (n i) → ℝ)
    (α : ℝ) : Prop :=
  DualFeasible u x η w α ∧ dualObj u x w α = lpValue u x η

/-- The dual player law `λ_i = Σ_a w_{i,a}` ((3.4), p.8). -/
def lam (w : (i : Fin m) → Fin (n i) → ℝ) (i : Fin m) : ℝ :=
  ∑ a, w i a

/-- The conditional mixed deviation `b_i = Σ_a w_{i,a} e_a / λ_i` when `λ_i > 0`, and the
smallest-indexed pure action (index `0`) when `λ_i = 0` ((3.4), p.8). -/
def bdev (w : (i : Fin m) → Fin (n i) → ℝ) : Mixed n :=
  fun i => if 0 < lam w i then (fun a => w i a / lam w i)
    else (fun a => if (a : ℕ) = 0 then 1 else 0)

/-- The weighted replacement column `F_j(y_j) = Σ_i λ_i d_{i,b_i}(x[j ← y_j])` ((4.4), (5.11)). -/
def Fcol (u : Utility n) (x : Mixed n) (w : (i : Fin m) → Fin (n i) → ℝ) (j : Fin m)
    (y : Fin (n j) → ℝ) : ℝ :=
  ∑ i, lam w i * deficitMix u (Function.update x j y) i (bdev w i)

end MultiNashRepair


