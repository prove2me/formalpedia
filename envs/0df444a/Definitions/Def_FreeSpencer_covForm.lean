-- Prove2me | Definitions.Def_FreeSpencer_covForm
-- name    : FreeSpencer_covForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:29.26014+00:00
-- url     : https://prove2.me/theorems/1295c6f4-63d0-4015-8b3d-e6b6517a693a
-- title:
--   The derivatives $J$, $\Gamma$, the no-spike condition, $\mathrm{Tr}(CJ)$
-- statement:
--   The center derivative and covariance derivative of the potential at a state $(H,C)$ are
--   $$J(u,u)=\tfrac12D_H^2E(H,C)[\hat A(u),\hat A(u)],\qquad \Gamma(u,w)=D_CE(H,C)\Bigl[\frac{uw^T+wu^T}{2}\Bigr],\quad u,w\in\mathrm{ran}\,C.$$
--   The no-spike condition with level $t$ is $\Gamma|_{\mathrm{ran}\,C}\preceq tI$. The averaged response is $\mathrm{Tr}(CJ)=\sum_aJ(C^{1/2}e_a,C^{1/2}e_a)$.
--
--   **Formalization Note** All derivatives are one-variable derivatives along lines of the supremum defining the potential. On $\mathrm{ran}\,C$ the two-sided covariance derivative exists, since the line stays on the coefficient face near $0$. A symmetric-part helper extends functions of symmetric matrices to the full space, for smoothness statements at interior points.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (5.3), p.31; p.24; p.31

import Mathlib
import Definitions.Def_FreeSpencer_pot
import Definitions.Def_FreeSpencer_covMap
import Definitions.Def_MatrixLewis_mpow
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- The symmetric part `(X + Xᵀ)/2`. It extends a function of symmetric matrices to the full matrix
space, so that smoothness on the open symmetric coefficient face is a statement at interior points. -/
noncomputable def symPart {α : Type*} [Fintype α] (X : Matrix α α ℝ) : Matrix α α ℝ :=
  (1 / 2 : ℝ) • (X + Xᵀ)

/-- The vectors of `ran C`. -/
def InRan {ℓ : ℕ} (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (u : Fin ℓ → ℝ) : Prop :=
  ∃ z, C *ᵥ z = u

/-- The second derivative of the potential at `H` in a matrix direction `B`:
`D²_H E(H, C)[B, B]`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (5.3), p.31. -/
noncomputable def centerHess {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (q θ κ : ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ)
    (B : Matrix ι ι ℝ) : ℝ :=
  deriv (deriv fun t : ℝ => pot q θ κ Ah (H + t • B) C) 0

/-- `J[u, u] = ½ D²_H E(H, C)[Â(u), Â(u)]`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (5.3), p.31.

**Formalization Note** `deriv` is `0` off differentiability. `lemma_5_1` and `theorem_D_1` assert
the smoothness that gives this its meaning. -/
noncomputable def halfCurv {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (q θ κ : ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ)
    (u : Fin ℓ → ℝ) : ℝ :=
  (1 / 2) * centerHess q θ κ Ah H C (aHat Ah u)

/-- The covariance derivative `Γ(u, w) = D_C E(H, C)[(u wᵀ + w uᵀ)/2]`, for `u, w ∈ ran C`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (5.3), p.31.

**Formalization Note** On `ran C` the two-sided derivative exists, since `C + ε(u wᵀ + w uᵀ)/2`
stays on the coefficient face for small `|ε|` (p.30). -/
noncomputable def covForm {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (q θ κ : ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ)
    (u w : Fin ℓ → ℝ) : ℝ :=
  deriv (fun ε : ℝ => pot q θ κ Ah H
    (C + ε • ((1 / 2 : ℝ) • (Matrix.vecMulVec u w + Matrix.vecMulVec w u)))) 0

/-- The no-spike condition `Γ|_{ran C} ⪯ t I`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), p.24 and eq. (6.20), p.48. -/
def NoSpike {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (q θ κ : ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (t : ℝ) : Prop :=
  ∀ u, InRan C u → covForm q θ κ Ah H C u u ≤ t * (u ⬝ᵥ u)

/-- The `a`-th column `C^{1/2} e_a` of the square root of the covariance. -/
noncomputable def covCol {ℓ : ℕ} (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (a : Fin ℓ) : Fin ℓ → ℝ :=
  fun i => MatrixLewis.mpow (1 / 2) C i a

/-- The averaged response `Tr(CJ) = ∑ₐ J(C^{1/2} eₐ, C^{1/2} eₐ)`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), p.31. -/
noncomputable def TrCJ {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (q θ κ : ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) : ℝ :=
  ∑ a, halfCurv q θ κ Ah H C (covCol C a)

end FreeSpencer


