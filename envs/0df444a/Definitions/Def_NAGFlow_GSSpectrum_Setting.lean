-- Prove2me | Definitions.Def_NAGFlow_GSSpectrum_Setting
-- name    : NAGFlow_GSSpectrum_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:07.259143+00:00
-- url     : https://prove2.me/theorems/adf2781e-1788-4da3-a33c-facc9423abda
-- title:
--   pp. 7, 9, 10, 35–36 — the quadratic model, σ and ρ over ℂ, G_HB and G_NAG of (39), the block Gauss–Seidel matrix E(α, G) of (42), E(α, R) of (124)
-- statement:
--   This file fixes the objects of Section 2 and Appendix A of Luo and Chen.
--
--   **Spectrum and spectral radius.** For a real square matrix $M$, $\sigma(M)$ is the set of all eigenvalues of $M$, which are in general complex; it is the spectrum of $M$ regarded as a complex matrix. The spectral radius is $\rho(M)=\max_{\lambda\in\sigma(M)}|\lambda|$. The predicate "$\rho(M)=r$" says that this maximum exists and equals $r$, i.e. $r$ is the greatest element of $\{|\lambda| : \lambda\in\sigma(M)\}$.
--
--   **The quadratic model.** $A$ is a real symmetric $d\times d$ matrix with
--   $$0\le \mu=\lambda_{\min}(A)\le\lambda\le\lambda_{\max}(A)=L\qquad\forall\,\lambda\in\sigma(A),$$
--   where $\mu$ and $L$ are themselves eigenvalues of $A$. When $\mu>0$ the condition number of $A$ is $\kappa(A)=L/\mu$.
--
--   **The transformations (39).** For $\mu>0$,
--   $$G_{\mathrm{HB}}=\begin{pmatrix}0 & I\\ -A/\mu & -2I\end{pmatrix},\qquad G_{\mathrm{NAG}}=\begin{pmatrix}-I & I\\ I-A/\mu & -I\end{pmatrix}.$$
--
--   **The Gauss–Seidel splitting (41)–(42).** For a $2\times 2$ block matrix $G$, $M$ is the block lower triangular part of $G$ (the two diagonal blocks and the lower-left block) and $N=G-M$; the one-step matrix of the scheme $(y_{k+1}-y_k)/\alpha=My_{k+1}+Ny_k$ is
--   $$E(\alpha,G)=(I-\alpha M)^{-1}(I+\alpha N).$$
--   For a real $2\times2$ matrix $R$, $E(\alpha,R)$ is defined in the same way with $M$ the lower triangular part of $R$, as in (124). The scalar model matrix of Appendix A is $R=\begin{pmatrix}-a & c\\ -b & -d\end{pmatrix}$, and the two reductions used on p. 36 are
--   $$R_{\mathrm{HB}}(\lambda)=\begin{pmatrix}0 & 1\\ -\lambda/\mu & -2\end{pmatrix},\qquad R_{\mathrm{NAG}}(\lambda)=\begin{pmatrix}-1 & 1\\ 1-\lambda/\mu & -1\end{pmatrix}.$$
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note.** The spectrum of a real matrix is taken over $\mathbb C$ (`spectrum ℂ` of the entrywise complexified matrix), because $E(\alpha,G)$ is not symmetric and its eigenvalues are complex. The spectral radius is not a function: "$\rho(M)=r$" is the predicate `IsGreatest`, and "$\rho(M)\le r$" is written eigenvalue by eigenvalue, so no junk value of a supremum over an empty set enters. The splitting of $G$ is blockwise, which is how the paper's own computation of $E(\alpha,G_{\mathrm{HB}})$ on p. 36 reads "lower triangular part"; the entrywise lower triangle would split $A$ itself. The matrix inverse in $E$ is Mathlib's, which is $0$ on a singular matrix; for $\alpha>0$ the matrices $I-\alpha M$ used here are block lower triangular with invertible diagonal blocks, so the inverse is the genuine one. $\kappa(A)$ is the number $L/\mu$, the paper's value of $\rho(A^{-1})\rho(A)$ for this model.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, §2 preamble p. 7; (39) p. 9; (41)–(42) p. 10; (124) p. 35; R(λ) p. 36

import Mathlib

namespace NAGFlow.GSSpectrum

open Matrix

/-- The spectrum σ(M) of a real square matrix `M`, i.e. the set of all its (complex) eigenvalues:
the spectrum of `M` regarded as a complex matrix (Luo & Chen, p. 7). -/
noncomputable def cspec {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : Set ℂ :=
  spectrum ℂ (M.map (algebraMap ℝ ℂ))

/-- `IsSpecRadius M r` says ρ(M) = r, where ρ(M) := max_{λ ∈ σ(M)} |λ| (p. 7): the maximum is
attained and equals `r` (in particular σ(M) is nonempty). -/
def IsSpecRadius {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) (r : ℝ) : Prop :=
  IsGreatest ((fun z : ℂ => ‖z‖) '' cspec M) r

/-- The standing quadratic model of Section 2 (p. 7): `A` is a real symmetric `d × d` matrix and
`0 ≤ μ = λ_min(A) ≤ λ ≤ λ_max(A) = L` for every `λ ∈ σ(A)`. -/
structure IsQuadModel {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (μ L : ℝ) : Prop where
  symm : A.IsHermitian
  mu_nonneg : 0 ≤ μ
  mu_mem : μ ∈ spectrum ℝ A
  L_mem : L ∈ spectrum ℝ A
  bounds : ∀ lam ∈ spectrum ℝ A, μ ≤ lam ∧ lam ≤ L

/-- The condition number κ(A) = L/μ of the model matrix when μ > 0 (p. 7). -/
noncomputable def kappa (μ L : ℝ) : ℝ := L / μ

/-- The one-step matrix of a splitting `G = M + N`: E := (I − αM)⁻¹(I + αN), as in (42), p. 10. -/
noncomputable def gsE {n : Type*} [Fintype n] [DecidableEq n] (α : ℝ) (M N : Matrix n n ℝ) :
    Matrix n n ℝ :=
  (1 - α • M)⁻¹ * (1 + α • N)

/-- The lower (block) triangular part of a `2 × 2` block matrix, diagonal blocks included. -/
def blockLower {n : Type*} (G : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  fromBlocks G.toBlocks₁₁ 0 G.toBlocks₂₁ G.toBlocks₂₂

/-- E(α, G) of (42), p. 10, for a `2 × 2` block matrix `G`: `M` is the block lower triangular part
of `G` (including the diagonal blocks) and `N = G − M`. -/
noncomputable def EG {n : Type*} [Fintype n] [DecidableEq n] (α : ℝ)
    (G : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  gsE α (blockLower G) (G - blockLower G)

/-- The lower triangular part of a real `2 × 2` matrix, diagonal included. -/
def lowerTri2 (R : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![R 0 0, 0; R 1 0, R 1 1]

/-- E(α, R) of (124), p. 35, for a real `2 × 2` matrix `R`: `M` is the lower triangular part of `R`
and `N = R − M`. -/
noncomputable def ER (α : ℝ) (R : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  gsE α (lowerTri2 R) (R - lowerTri2 R)

/-- The scalar model matrix R = (−a c ; −b −d) of Appendix A, p. 35. -/
def Rmat (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-a, c; -b, -d]

/-- G_HB = (0 I ; −A/μ −2I) of (39), p. 9. -/
noncomputable def GHB {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (μ : ℝ) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ :=
  fromBlocks 0 1 (-(μ⁻¹ • A)) (-(2 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ))

/-- G_NAG = (−I I ; I − A/μ −I) of (39), p. 9. -/
noncomputable def GNAG {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (μ : ℝ) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ :=
  fromBlocks (-1) 1 (1 - μ⁻¹ • A) (-1)

/-- R(λ) = (0 1 ; −λ/μ −2), the `2 × 2` reduction of G_HB at an eigenvalue λ of A (p. 36). -/
noncomputable def RHB (lam μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -(lam / μ), -2]

/-- R(λ) = (−1 1 ; 1 − λ/μ −1), the `2 × 2` reduction of G_NAG at an eigenvalue λ of A
(R_NAG of p. 9 with θ = λ/μ). -/
noncomputable def RNAG (lam μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1, 1; 1 - lam / μ, -1]

end NAGFlow.GSSpectrum


