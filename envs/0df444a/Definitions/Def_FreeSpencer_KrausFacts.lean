-- Prove2me | Definitions.Def_FreeSpencer_KrausFacts
-- name    : FreeSpencer_KrausFacts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:30.045826+00:00
-- url     : https://prove2.me/theorems/d123a9be-a8ab-499e-91ad-5747dcc0ac6f
-- title:
--   Balanced coordinates and the facts of Lemma 5.5
-- statement:
--   With $B'_a=\hat A(C^{1/2}e_a)$: the balanced density $P=Z^{-1/2}SZ^{-1/2}$, $R=Z^{-1/2}\sqrt SZ^{-1/2}$, and $D_a=Z^{1/2}B'_aZ^{1/2}$; the form $\Gamma(S)(u,w)=\mathrm{Tr}(S\hat A(u)Z\hat A(w))$; and the conjunction of the conclusions of Lemma 5.5 for a given bilinear form: $\Phi(P)=P$; $\langle F_a,F_b\rangle=\mathrm{Tr}(PD_aD_b)=\Gamma(C^{1/2}e_a,C^{1/2}e_b)$; $0\preceq\Sigma\preceq t\,\mathrm{Id}$; $\mathrm{Tr}_{HS}\Sigma=\mathrm{Tr}\,P=F(S,\eta_C(S))=\mathrm{Tr}(C\Gamma)\le\sqrt\ell$; and $\mathrm{Tr}\,R^2\le\mathrm{Tr}\,\eta_C(S)\le\ell$.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (5.9), p.34; Lemma 5.5, pp.36–37; (5.8), p.32

import Mathlib
import Definitions.Def_FreeSpencer_transport
import Definitions.Def_FreeSpencer_Sigma
import Definitions.Def_FreeSpencer_covForm
import Definitions.Def_FreeSpencer_fidelity
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- The Kraus matrix `B'ₐ = ∑ᵢ (C^{1/2})ᵢₐ Âᵢ = Â(C^{1/2} eₐ)`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), p.28; Lemma 5.4, p.34. -/
noncomputable def krausB {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ)
    (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (a : Fin ℓ) : Matrix ι ι ℝ :=
  aHat Ah (covCol C a)

/-- The balanced density `P = Z^{-1/2} S Z^{-1/2}`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (5.9), p.34. -/
noncomputable def balP {ι : Type*} [Fintype ι] [DecidableEq ι] (Z S : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  MatrixLewis.mpow (-(1 / 2)) Z * S * MatrixLewis.mpow (-(1 / 2)) Z

/-- `R = Z^{-1/2} √S Z^{-1/2}`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (5.9), p.34. -/
noncomputable def balR {ι : Type*} [Fintype ι] [DecidableEq ι] (Z S : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  MatrixLewis.mpow (-(1 / 2)) Z * MatrixLewis.mpow (1 / 2) S * MatrixLewis.mpow (-(1 / 2)) Z

/-- The conjugated Kraus matrices `Dₐ = Z^{1/2} B'ₐ Z^{1/2}`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (5.9), p.34. -/
noncomputable def balD {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ)
    (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (Z : Matrix ι ι ℝ) (a : Fin ℓ) : Matrix ι ι ℝ :=
  MatrixLewis.mpow (1 / 2) Z * krausB Ah C a * MatrixLewis.mpow (1 / 2) Z

/-- `Γ(S)(u, w) = Tr(S Â(u) Z Â(w))`, the right side of (5.8) at a density `S` and transport `Z`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (5.8), p.32; Lemma 5.5, p.37. -/
def gammaAt {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ)
    (S Z : Matrix ι ι ℝ) (u w : Fin ℓ → ℝ) : ℝ :=
  Matrix.trace (S * aHat Ah u * Z * aHat Ah w)

/-- The conclusions (5.13), (5.14) of Lemma 5.5 at a positive definite `S` with transport `Z`,
for a bilinear form `Γ` on coefficient vectors, under `Γ|_{ran C} ⪯ t I`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.5, pp.36–37. -/
def KrausFacts {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ)
    (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (S Z : Matrix ι ι ℝ) (t : ℝ)
    (Γ : (Fin ℓ → ℝ) → (Fin ℓ → ℝ) → ℝ) : Prop :=
  let P := balP Z S
  let R := balR Z S
  let D := balD Ah C Z
  let M := covMap Ah C S
  opPhi D P = P ∧
  (∀ a b, hs (normKraus P (D a)) (normKraus P (D b)) = Matrix.trace (P * D a * D b)) ∧
  (∀ a b, Γ (covCol C a) (covCol C b) = Matrix.trace (P * D a * D b)) ∧
  (∀ X, 0 ≤ hs X (opSigma P D X) ∧ hs X (opSigma P D X) ≤ t * hs X X) ∧
  trHS (opSigma P D) = Matrix.trace P ∧
  Matrix.trace P = fidelity S M ∧
  fidelity S M = ∑ a, Γ (covCol C a) (covCol C a) ∧
  ∑ a, Γ (covCol C a) (covCol C a) ≤ Real.sqrt ℓ ∧
  Matrix.trace (R * R) ≤ Matrix.trace M ∧
  Matrix.trace M ≤ ℓ

end FreeSpencer


