-- Prove2me | Definitions.Def_QKPSDP_IsGlobalOptSQKELR
-- name    : QKPSDP_IsGlobalOptSQKELR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:52.692437+00:00
-- url     : https://prove2.me/theorems/ea8502d6-08aa-4dd8-b196-5f936d1ceca2
-- title:
--   Global optimal solutions of (SQKELR)
-- statement:
--   The low-rank problem (SQKELR) is $\min\{-\langle C, RR^\top\rangle : R \in \mathcal K_{n,r}\}$. A matrix $R \in \mathbb R^{n\times r}$ is a **global optimal solution** if $R \in \mathcal K_{n,r}$ and
--
--   $$
--   -\langle C, RR^\top\rangle \le -\langle C, R'R'^\top\rangle \quad\text{for every } R' \in \mathcal K_{n,r}.
--   $$
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, (SQKELR), p.3

import Mathlib
import Definitions.Def_QKPSDP_K

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, (SQKELR), p.3: `R` is a *global optimal solution* of
`(SQKELR) min { −⟨C, RR⊤⟩ : ‖a⊤R‖² − τa⊤Re₁ = 0, diag(RR⊤) = Re₁, R ∈ ℝ^{n×r} }`:
`R ∈ K_{n,r}` and `−⟨C, RR⊤⟩ ≤ −⟨C, R'R'⊤⟩` for every `R' ∈ K_{n,r}` (same `r`).

**Formalization Note** `⟨A, B⟩ := Tr(AB⊤)` (p.4) is `(A * Bᵀ).trace`. -/
def IsGlobalOptSQKELR {n r : ℕ} [NeZero r] (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (τ : ℝ) (R : Matrix (Fin n) (Fin r) ℝ) : Prop :=
  R ∈ K a τ ∧ ∀ R' : Matrix (Fin n) (Fin r) ℝ, R' ∈ K a τ →
    -(C * (R * Rᵀ)ᵀ).trace ≤ -(C * (R' * R'ᵀ)ᵀ).trace

end QKPSDP


