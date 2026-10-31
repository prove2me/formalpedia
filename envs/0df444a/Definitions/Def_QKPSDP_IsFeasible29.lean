-- Prove2me | Definitions.Def_QKPSDP_IsFeasible29
-- name    : QKPSDP_IsFeasible29
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:46.330071+00:00
-- url     : https://prove2.me/theorems/8f4288ed-f56f-47a9-88b3-5e9ffd86c900
-- title:
--   Feasible points of the SDP (29)
-- statement:
--   For $R = ve_1^\top \in \mathcal N_{n,r}$, the SDP (29) is
--
--   $$
--   \min\Bigl\{ \bigl\langle 2\operatorname{diag}((Cv)\circ d) - C,\ X\bigr\rangle :\ \bigl\langle aa^\top - \sigma_v\tau\operatorname{diag}(a\circ d),\ X\bigr\rangle = 0,\ \operatorname{Tr}(X) = 1,\ X \in \mathbb S^n_+ \Bigr\}.
--   $$
--
--   $X$ is **feasible** if it satisfies the three constraints.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, (29), p.13; (43), p.15

import Mathlib
import Definitions.Def_QKPSDP_con29

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, (29), p.13 (and (43), p.15): `X` is feasible for the SDP
`min { ⟨2diag((Cv) ∘ d) − C, X⟩ : ⟨aa⊤ − σ_vτ · diag(a ∘ d), X⟩ = 0, Tr(X) = 1, X ∈ S₊ⁿ }`.

**Formalization Note** `⟨A, X⟩ = Tr(AX⊤)` is `(A * Xᵀ).trace`; `X ∈ S₊ⁿ` is
`Matrix.PosSemidef` (symmetry included). -/
def IsFeasible29 {n : ℕ} (a : Fin n → ℝ) (τ : ℝ) (v : Fin n → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (con29 a τ v * Xᵀ).trace = 0 ∧ X.trace = 1 ∧ X.PosSemidef

end QKPSDP


