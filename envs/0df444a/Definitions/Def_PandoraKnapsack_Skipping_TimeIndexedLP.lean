-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_TimeIndexedLP
-- name    : PandoraKnapsack_Skipping_TimeIndexedLP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:23:36.245746+00:00
-- url     : https://prove2.me/theorems/6b68030a-ab4f-44f7-8af0-32df1da34294
-- title:
--   The time-indexed linear program Ψ(b)
-- statement:
--   For a horizon $b\in\mathbb N$, the linear program $\Psi(b)$ is
--   $$\max_x\ \sum_{i,j}\sum_{t=0}^{b} w_{i,j,t}\,x_{i,j,t}$$
--   subject to (8) $\sum_{i,j}\sum_{t'\le t}x_{i,j,t'}\,\mu_{i,j,t}\le 2t$ for every $t\in\{0,\dots,b\}$, (9) $\sum_j\sum_{t\le b}x_{i,j,t}\le1$ for every item $i$, and (10) $0\le x_{i,j,t}\le1$.
--
--   `PsiFeasible I b x` states (8)–(10), `psiObjective I b x` is the objective, and `PsiOptimal I b x` says $x$ is feasible with objective at least that of every feasible point. A candidate is an array indexed by $(i,j,t)$ with $t\in\mathbb N$; coordinates with $t>b$ are ignored. The capacity $T$ inside $w$ is the instance's, whatever $b$ is.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen (2026), Pandora's Knapsack via Simple Policies, supplied PDF (STOC 2027 submission), SHA256 45e5830b173d687c08d5175988af81bf660c693ff805b1d2e7bc213140d27a2d, §5.1, equations (8)–(10), printed pp. 21–22 (PDF 23–24)

import Definitions.Def_PandoraKnapsack_Skipping_Instance

namespace PandoraKnapsack.Skipping

/-- **The time-indexed linear program `Ψ(b)`**, equations (8)–(10).

Barak et al. (2026), *Pandora's Knapsack via Simple Policies*, supplied PDF (SHA256
45e5830b…7a2d), §5.1, printed pp. 21–22 (PDF 23–24):
`Ψ(b) = max Σ_{i,j} Σ_{t ≤ b} w_{i,j,t} x_{i,j,t}` subject to
(8) `Σ_{i,j} Σ_{t' ≤ t} x_{i,j,t'} μ_{i,j,t} ≤ 2t` for every `t ∈ {0, …, b}`,
(9) `Σ_j Σ_{t ≤ b} x_{i,j,t} ≤ 1` for every item `i`,
(10) `0 ≤ x_{i,j,t} ≤ 1`.

**Formalization Note.** A candidate solution is an array `Fin n → Fin m → ℕ → ℝ`; only the
coordinates `t ∈ {0, …, b}` enter the constraints and the objective, the others are ignored.
`b` is the horizon of the index set; the capacity `T` inside `w` and the instance stays the
instance's. Optimality is stated against every feasible point; no supremum is taken. -/
abbrev LPArray (n m : ℕ) := Fin n → Fin m → ℕ → ℝ

variable {n m T : ℕ}

/-- Feasibility for `Ψ(b)`: constraints (8), (9), (10). -/
def PsiFeasible (I : Instance n m T) (b : ℕ) (x : LPArray n m) : Prop :=
  (∀ t, t ≤ b →
      ∑ i, ∑ j, ∑ t' ∈ Finset.range (t + 1), x i j t' * mu I i j t ≤ 2 * (t : ℝ)) ∧
  (∀ i, ∑ j, ∑ t ∈ Finset.range (b + 1), x i j t ≤ 1) ∧
  (∀ i j t, t ≤ b → 0 ≤ x i j t ∧ x i j t ≤ 1)

/-- The objective `Σ_{i,j} Σ_{t ≤ b} w_{i,j,t} x_{i,j,t}` of `Ψ(b)`. -/
noncomputable def psiObjective (I : Instance n m T) (b : ℕ) (x : LPArray n m) : ℝ :=
  ∑ i, ∑ j, ∑ t ∈ Finset.range (b + 1), effWeight I i j t * x i j t

/-- `x` is an optimal solution of `Ψ(b)`. -/
def PsiOptimal (I : Instance n m T) (b : ℕ) (x : LPArray n m) : Prop :=
  PsiFeasible I b x ∧ ∀ y, PsiFeasible I b y → psiObjective I b y ≤ psiObjective I b x

end PandoraKnapsack.Skipping


