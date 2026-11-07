-- Prove2me | Definitions.Def_FreeSpencer_specProj
-- name    : FreeSpencer_specProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:00.573166+00:00
-- url     : https://prove2.me/theorems/de222e30-2a70-449c-9579-3f3f30974f2a
-- title:
--   The spectral split and the high-part matrix $W_h$
-- statement:
--   For $\epsilon>0$: the spectral projection $\Pi_h=\mathbb 1_{[\epsilon,\infty)}(P)$; the high part $D^h=\Pi_hD\Pi_h$ and the low part $D^l=D-\Pi_hD\Pi_h$ of a Kraus matrix; the Tsallis-only half-response $q_\theta(D)=\theta^{-1}\|P^{1/2}DR^{1/2}\|_{HS}^2$; the matrix $W_h=\sum_a\Phi(D_a^h)P\Phi(D_a^h)$; and the Gram matrix $G_{ab}=\mathrm{Tr}(PD_aD_b)$.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (6.9), Lemma 6.2, p.44; Lemma 6.1, p.42; Lemma 6.3, p.45

import Mathlib
import Definitions.Def_FreeSpencer_Sigma
import Definitions.Def_MatrixLewis_mpow
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- The spectral projection `Π_h = 1_{[ε,∞)}(P)`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), p.44. -/
noncomputable def specProj {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ℝ) (P : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  cfc (fun x : ℝ => if ε ≤ x then (1 : ℝ) else 0) P

/-- The high part `Dʰ = Π_h D Π_h`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (6.9), p.44. -/
noncomputable def highPart {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ℝ) (P D : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  specProj ε P * D * specProj ε P

/-- The low part `Dˡ = D - Π_h D Π_h` (equal to `Π_l D + Π_h D Π_l`).
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (6.9), p.44. -/
noncomputable def lowPart {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ℝ) (P D : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  D - highPart ε P D

/-- The Tsallis-only half-response `q_θ(D) = θ⁻¹ ‖P^{1/2} D R^{1/2}‖²_HS`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 6.2, p.44. -/
noncomputable def qTheta {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ℝ) (P R D : Matrix ι ι ℝ) : ℝ :=
  θ⁻¹ * hs (MatrixLewis.mpow (1 / 2) P * D * MatrixLewis.mpow (1 / 2) R) (MatrixLewis.mpow (1 / 2) P * D * MatrixLewis.mpow (1 / 2) R)

/-- `W_h = ∑ₐ Φ(Dₐʰ) P Φ(Dₐʰ)`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 6.3, p.45. -/
noncomputable def highW {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (ε : ℝ) (P : Matrix ι ι ℝ)
    (D : Fin r → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  ∑ a, opPhi D (highPart ε P (D a)) * P * opPhi D (highPart ε P (D a))

/-- The real Gram matrix `G_{ab} = Tr(P Dₐ D_b)`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 6.1, p.42. -/
noncomputable def gramG {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (P : Matrix ι ι ℝ)
    (D : Fin r → Matrix ι ι ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun a b => Matrix.trace (P * D a * D b)

end FreeSpencer


