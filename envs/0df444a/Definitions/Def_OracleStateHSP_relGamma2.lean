-- Prove2me | Definitions.Def_OracleStateHSP_relGamma2
-- name    : OracleStateHSP_relGamma2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:31.335604+00:00
-- url     : https://prove2.me/theorems/76499342-540b-4ea0-8fb3-7bcdccf12acb
-- title:
--   Relative $\gamma_2$ norm $\gamma_2(A \mid \Delta)$
-- statement:
--   For an $X \times X$ matrix $A$ and a family $\Delta = (\Delta_{xy})_{x,y \in X}$ of matrices on $\mathcal H_S$, the **relative $\gamma_2$ norm** is
--   $$
--   \gamma_2(A \mid \Delta) = \inf \Bigl\{ \max\Bigl(\sup_x \|u_x\|^2,\ \sup_y \|v_y\|^2\Bigr) \Bigr\},
--   $$
--   the infimum over all $k \in \mathbb N$ and all vectors $u_x, v_y \in \mathcal H_S \otimes \mathbb C^k$ such that
--   $$
--   A_{xy} = \langle u_x, (\Delta_{xy} \otimes I_k)\, v_y \rangle \quad \text{for all } x, y \in X .
--   $$
--   It is the value of the semidefinite program that finds a minimum-cost factorization of each entry $A_{xy}$ through $\Delta_{xy}$.
--
--   The paper uses the norm as a black box from Belovs (*Variations on quantum adversary*, arXiv:1504.06943), through Theorem 4.4 and Fact 4.5.
--
--   **Formalization Note** The paper gives no formula; this is Belovs's definition. The value lies in $[0, \infty]$ (`ℝ≥0∞`): an infeasible program (for instance $\Delta_{xy} = 0$ with $A_{xy} \ne 0$) has value $\infty$. The objective $\max(\max\|u_x\|^2, \max\|v_y\|^2)$ equals the product form $\max_x\|u_x\| \cdot \max_y\|v_y\|$ after rescaling $u \mapsto tu$, $v \mapsto v/t$, so the two common forms define the same norm. The inner product is conjugate-linear in its first argument.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, §4.1, p.36 (definition from A. Belovs, Variations on quantum adversary, arXiv:1504.06943)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
open scoped ENNReal

namespace OracleStateHSP

open QAlgorithms

/-- The relative `γ₂` norm `γ₂(A | Δ)` of a matrix `A = (A_xy)` with respect to a family of matrices
`Δ = (Δ_xy)` on the query register (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, §4.1, p.36, used there as a black box from
A. Belovs, *Variations on quantum adversary*, arXiv:1504.06943, 2015): the least cost of a
factorization of every entry through `Δ_xy`,
`γ₂(A | Δ) = inf max( sup_x ‖u_x‖², sup_y ‖v_y‖² )` over all `k` and all vectors
`u_x, v_y ∈ H_S ⊗ ℂ^k` with `A_xy = ⟨u_x, (Δ_xy ⊗ I_k) v_y⟩` for all `x, y`.

**Formalization Note.** The paper does not define the norm; this is Belovs's definition (the
"minimum-cost factorization of each entry `A_x,y` as an inner product through the matrix `Δ_xy`"
of p.36). The auxiliary space is `ℂ^k` for a finite `k`. The value is the infimum in `ℝ≥0∞`: an
infeasible program (for instance `Δ_xy = 0` with `A_xy ≠ 0`) has value `⊤`. The objective
`max(max‖u_x‖², max‖v_y‖²)` equals the product form `max_x‖u_x‖ · max_y‖v_y‖` after rescaling
`u ↦ t u`, `v ↦ v / t`, so both forms give the same norm. The inner product is conjugate-linear in
its first argument. -/
noncomputable def relGamma2 {X Q : Type*} [Fintype Q] (A : Matrix X X ℂ)
    (Δ : X → X → Matrix Q Q ℂ) : ℝ≥0∞ :=
  ⨅ (k : ℕ) (u : X → EuclideanSpace ℂ (Q × Fin k)) (v : X → EuclideanSpace ℂ (Q × Fin k))
    (_ : ∀ x y, A x y =
      inner ℂ (u x) (act (Matrix.kronecker (Δ x y) (1 : Matrix (Fin k) (Fin k) ℂ)) (v y))),
    max (⨆ x, ENNReal.ofReal (‖u x‖ ^ 2)) (⨆ y, ENNReal.ofReal (‖v y‖ ^ 2))

end OracleStateHSP


