-- Prove2me | Definitions.Def_AvgValueAlloc_Hobj
-- name    : AvgValueAlloc_Hobj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:25.478417+00:00
-- url     : https://prove2.me/theorems/8aa686cb-4711-4837-aff7-317047368e2a
-- title:
--   Funding objective $H_{\hat V}(M)$ and scores $s_j$ of (6)
-- statement:
--   A **zero-at-zero diminishing-returns objective** $\hat V$ on banks $B\ge0$ satisfies $\hat V(0)=0$, is monotone, and has bank-coordinate diminishing returns: $\hat V(C+\delta e_j)-\hat V(C)\le\hat V(B+\delta e_j)-\hat V(B)$ for $0\le B\le C$, $\delta\ge0$. Define
--   $$
--   s_j=v_j+\hat V\bigl(B+(v_j-\rho_j)e_j\bigr)-\hat V(B),\qquad H_{\hat V}(M)=\max_X\{W(X)+\hat V(B(X))\}.\tag{6}
--   $$
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2.1, p.5, eq. (6)

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_welfare
import Definitions.Def_AvgValueAlloc_posSet
import Definitions.Def_AvgValueAlloc_routBank

namespace AvgValueAlloc

/-- A zero-at-zero diminishing-returns objective on nonnegative banks: `V(0) = 0`, `V` monotone,
and bank-coordinate diminishing returns `V(C + δe_j) − V(C) ≤ V(B + δe_j) − V(B)` for
`0 ≤ B ≤ C`, `δ ≥ 0`. -/
def IsDRObjective {n : ℕ} (V : (Fin n → ℝ) → ℝ) : Prop :=
  V 0 = 0 ∧ (∀ B C, 0 ≤ B → B ≤ C → V B ≤ V C) ∧
    (∀ B C, 0 ≤ B → B ≤ C → ∀ (j : Fin n) (δ : ℝ), 0 ≤ δ →
      V (C + δ • Pi.single j 1) - V C ≤ V (B + δ • Pi.single j 1) - V B)

/-- **The funding objective `H_V̂(M)` of (6).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2.1, p.5, (6): "For a zero-at-zero
diminishing-returns objective V̂, define s_j = v_j + V̂(B + (v_j − ρ_j)e_j) − V̂(B),
H_V̂(M) = max_X {W(X) + V̂(B(X))}."

`Hobj ρ V M = max over routings X of M of W(X) + V(B(X))`.

**Formalization Note.** A real `⨆` over the finite nonempty type of routings (rejecting every item
is a routing), hence a maximum. -/
noncomputable def Hobj {n m : ℕ} (ρ : Fin n → ℚ) (V : (Fin n → ℝ) → ℝ) (M : Fin m → Vec n) : ℝ :=
  ⨆ X : {X : Fin m → Option (Fin n) // IsRouting ρ M X}, welfare M X.1 + V (routBank ρ M X.1)

/-- The score `s_j = v_j + V(B + (v_j − ρ_j)e_j) − V(B)` of (6). -/
noncomputable def score {n : ℕ} (ρ : Fin n → ℚ) (V : (Fin n → ℝ) → ℝ) (B : Fin n → ℝ)
    (u : Vec n) (j : Fin n) : ℝ :=
  ((u j : ℚ≥0) : ℝ) + V (B + (((u j : ℚ≥0) : ℝ) - ρ j) • Pi.single j 1) - V B

/-- The maximum score over `J(u)`, `0` if `J(u) = ∅`. -/
noncomputable def maxScore {n : ℕ} (ρ : Fin n → ℚ) (V : (Fin n → ℝ) → ℝ) (B : Fin n → ℝ)
    (u : Vec n) : ℝ :=
  if h : (posSet ρ u).Nonempty then (posSet ρ u).sup' h (score ρ V B u) else 0

end AvgValueAlloc


