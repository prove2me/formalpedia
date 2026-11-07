-- Prove2me | Definitions.Def_FreeSpencer_Sigma
-- name    : FreeSpencer_Sigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:04:13.142219+00:00
-- url     : https://prove2.me/theorems/a16f7679-20d3-4b54-9b36-019923352b96
-- title:
--   The operators $\Phi$, $\Sigma$, $T$, $\tilde H$, $K_0$
-- statement:
--   For positive definite $P,R$ and real symmetric $D_1,\dots,D_r$: $\Phi(X)=\sum_aD_aXD_a$, the normalized Kraus matrices $F_a=2^{-1/2}J_P^{1/2}(D_a)$, the frame operator $\Sigma=\sum_a|F_a\rangle\langle F_a|$,
--   $$T=J_P^{-1/2}\Phi J_P^{1/2},\quad \tilde H_\theta^{-1}=\theta^{-1}J_P^{-1/2}(L_PR_R+L_RR_P)J_P^{-1/2},\quad \tilde H=(\mathrm{Id}-T)^*(\mathrm{Id}-T)+\tilde H_\theta,\quad K_0=T\tilde H_\theta^{-1}T^*,$$
--   all on the full real matrix Hilbert space with $\langle X,Y\rangle=\mathrm{Tr}(X^TY)$, and $\mathrm{Tr}_{HS}$ the trace of a linear operator on that space.
--
--   **Formalization Note** $T^*=J_P^{1/2}\Phi J_P^{-1/2}$, since $\Phi$ and $J_P^{\pm1/2}$ are self-adjoint when the $D_a$ are symmetric (p.36). Inverses are inverses in the ring of linear maps.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eqs. (5.9)–(5.12), pp.34–36; (6.1)–(6.3), p.42; p.27

import Mathlib
import Definitions.Def_FreeSpencer_JPow
import Definitions.Def_MatrixLewis_mpow
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- The Hilbert–Schmidt inner product `⟨X, Y⟩ = Tr(Xᵀ Y)`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), p.19. -/
def hs {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℝ) : ℝ := Matrix.trace (Xᵀ * Y)

/-- The rank-one operator `|U⟩⟨U| : X ↦ U ⟨U, X⟩`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), p.27. -/
noncomputable def ketBra {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℝ) :
    Module.End ℝ (Matrix ι ι ℝ) :=
  { toFun := fun X => hs U X • U
    map_add' := fun X Y => by simp [hs, Matrix.mul_add, Matrix.trace_add, add_smul]
    map_smul' := fun c X => by simp [hs, Matrix.trace_smul, mul_smul] }

/-- The map `Φ(X) = ∑ₐ Dₐ X Dₐ`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (5.9), p.34; Section 6, p.41. -/
noncomputable def opPhi {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (D : Fin r → Matrix ι ι ℝ) :
    Module.End ℝ (Matrix ι ι ℝ) :=
  ∑ a, LinearMap.mulLeft ℝ (D a) ∘ₗ LinearMap.mulRight ℝ (D a)

/-- The normalized Kraus matrix `F(D) = 2^{-1/2} J_P^{1/2}(D)`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eqs. (5.12), (6.1), pp.36, 42. -/
noncomputable def normKraus {ι : Type*} [Fintype ι] [DecidableEq ι] (P D : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (Real.sqrt 2)⁻¹ • JPow P (1 / 2) D

/-- The frame operator `Σ = ∑ₐ |Fₐ⟩⟨Fₐ|` of the normalized Kraus matrices of `D`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eqs. (5.12), (6.1), pp.36, 42. -/
noncomputable def opSigma {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (P : Matrix ι ι ℝ)
    (D : Fin r → Matrix ι ι ℝ) : Module.End ℝ (Matrix ι ι ℝ) :=
  ∑ a, ketBra (normKraus P (D a))

/-- `T = J_P^{-1/2} Φ J_P^{1/2}`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eqs. (5.11), (6.2), pp.35, 42. -/
noncomputable def opT {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (P : Matrix ι ι ℝ)
    (D : Fin r → Matrix ι ι ℝ) : Module.End ℝ (Matrix ι ι ℝ) :=
  JPow P (-(1 / 2)) * opPhi D * JPow P (1 / 2)

/-- `T∗ = J_P^{1/2} Φ J_P^{-1/2}`, the adjoint of `T`, since `Φ` and `J_P^{±1/2}` are self-adjoint.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), proof of Lemma 5.4, p.36. -/
noncomputable def opTstar {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (P : Matrix ι ι ℝ)
    (D : Fin r → Matrix ι ι ℝ) : Module.End ℝ (Matrix ι ι ℝ) :=
  JPow P (1 / 2) * opPhi D * JPow P (-(1 / 2))

/-- `H̃_θ⁻¹ = θ⁻¹ J_P^{-1/2} (L_P R_R + L_R R_P) J_P^{-1/2}`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (6.2), p.42. -/
noncomputable def opHthetaInvTilde {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ℝ) (P R : Matrix ι ι ℝ) :
    Module.End ℝ (Matrix ι ι ℝ) :=
  θ⁻¹ • (JPow P (-(1 / 2)) *
    (LinearMap.mulLeft ℝ P ∘ₗ LinearMap.mulRight ℝ R + LinearMap.mulLeft ℝ R ∘ₗ LinearMap.mulRight ℝ P) *
    JPow P (-(1 / 2)))

/-- `H̃ = (Id - T)∗(Id - T) + H̃_θ`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eqs. (5.11), (6.3), pp.35, 42.

**Formalization Note** `Ring.inverse` is the inverse in the ring of linear maps; it is `0` on a
non-unit. For `P, R ≻ 0` the operator of (6.2) is strictly positive, so it is a unit, on the full
real matrix space, which is the space Section 6 works on (p.41). -/
noncomputable def opHtilde {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (θ : ℝ) (P R : Matrix ι ι ℝ)
    (D : Fin r → Matrix ι ι ℝ) : Module.End ℝ (Matrix ι ι ℝ) :=
  (1 - opTstar P D) * (1 - opT P D) + Ring.inverse (opHthetaInvTilde θ P R)

/-- `K₀ = T H̃_θ⁻¹ T∗`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (6.3), p.42. -/
noncomputable def opK0 {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (θ : ℝ) (P R : Matrix ι ι ℝ)
    (D : Fin r → Matrix ι ι ℝ) : Module.End ℝ (Matrix ι ι ℝ) :=
  opT P D * opHthetaInvTilde θ P R * opTstar P D

/-- The trace `Tr_HS` of a linear operator on the matrix space. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), p.27. -/
noncomputable def trHS {ι : Type*} [Fintype ι] [DecidableEq ι] (O : Module.End ℝ (Matrix ι ι ℝ)) : ℝ :=
  LinearMap.trace ℝ (Matrix ι ι ℝ) O

end FreeSpencer


