-- Prove2me | Definitions.Def_Arxiv1605_04704_Basic
-- name    : Arxiv1605_04704_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T19:52:38.297843+00:00
-- url     : https://prove2.me/theorems/083a5b7d-2ffb-47c8-96a5-2fa77806aef4
-- title:
--   Mueller matrices: covariance matrix, parallel decompositions, indices of polarimetric purity and covariance/noise filtering
-- statement:
--   Objects of Sections 2, 4 and 5 of Gil, *On optimal filtering of measured Mueller matrices* (arXiv:1605.04704v3).
--
--   1. **Covariance matrix (eq. 2).** To a real $4\times4$ matrix $M=(m_{kl})_{k,l=0}^{3}$ is associated the Hermitian $4\times4$ matrix $H(M)$ of eq. (2), whose trace is $m_{00}$. The map $M\mapsto H(M)$ is a linear bijection onto the Hermitian matrices, and $M(H)$ denotes its inverse. $M$ satisfies the covariance criterion when $H(M)$ is positive semidefinite.
--   2. **Spectral data (eqs. 3-4).** $U$ is a unitary matrix with columns $u_0,\dots,u_3$, and $\hat\lambda_0\ge\hat\lambda_1\ge\hat\lambda_2\ge\hat\lambda_3$ are numbers such that $H(M)=m_{00}\,U\operatorname{diag}(\hat\lambda_0,\hat\lambda_1,\hat\lambda_2,\hat\lambda_3)U^\dagger$. These are the normalized eigenvalues $\hat\lambda_i=\lambda_i/\operatorname{tr}H$ and the eigenvectors of $H$.
--   3. **Pure parallel decompositions (eqs. 6, 13).** A decomposition of $M$ into $n$ pure components is $H(M)=\sum_{i<n}p_i\,m_{00}\,w_i\otimes w_i^\dagger$ with $p_i\ge0$, $\sum_ip_i=1$, and $w_i$ linearly independent unit vectors of $\mathbb{C}^4$ in $\operatorname{Range}H(M)$. An *arbitrary decomposition* is such a decomposition with $n=r=\operatorname{rank}H(M)$.
--   4. **Components (eqs. 8, 10, 14, 15).** The spectral components are $M_{Ui}=M(m_{00}\,u_i\otimes u_i^\dagger)$. The 2D and 3D depolarizers are $M_2=M\big(\tfrac12m_{00}U\operatorname{diag}(1,1,0,0)U^\dagger\big)$ and $M_3=M\big(\tfrac13m_{00}U\operatorname{diag}(1,1,1,0)U^\dagger\big)$. The ideal depolarizer is $M_{\Delta0}=m_{00}\operatorname{diag}(1,0,0,0)$.
--   5. **Indices of polarimetric purity (eq. 11).** $P_1=\hat\lambda_0-\hat\lambda_1$, $P_2=\hat\lambda_0+\hat\lambda_1-2\hat\lambda_2$ and $P_3=\hat\lambda_0+\hat\lambda_1+\hat\lambda_2-3\hat\lambda_3$.
--   6. **Covariance filtering (Section 4, eq. 23).** For a measured $M_{\exp}$, $U$ diagonalizes $H_{\exp}=H(M_{\exp})=U\operatorname{diag}(\lambda_{\exp,0},\dots,\lambda_{\exp,3})U^\dagger$ with $\lambda_{\exp,0}\ge\dots\ge\lambda_{\exp,3}$. The filtered eigenvalues are $\lambda_{\mathrm{cov},i}=\max(\lambda_{\exp,i},0)$, and $H_{\mathrm{cov}}=U\operatorname{diag}(\lambda_{\mathrm{cov},i})U^\dagger$, $M_{\mathrm{cov}}=M(H_{\mathrm{cov}})$. The normalized eigenvalues of $M_{\mathrm{cov}}$ are $\hat\lambda_i=\lambda_{\mathrm{cov},i}/\sum_j\lambda_{\mathrm{cov},j}$.
--   7. **Noise filtering (Section 5, eqs. 24, 27).** With $P_i$, $m_{00}$, $M_{\Delta0}$ and $M_3$ those of $M_{\mathrm{cov}}$: $M_f^{(3)}=[M_{\mathrm{cov}}-(1-P_3)M_{\Delta0}]/P_3$ (case $q=3$) and $M_f^{(2)}=[M_{\mathrm{cov}}-(1-P_3)M_{\Delta0}-(P_3-P_2)M_3]/P_2$ (case $q=2$).
--
--   **Formalization Note** $M(H)$ is defined as the inverse function of $M\mapsto H(M)$ (Lean's `Function.invFun`). It is the paper's $M(H)$ on Hermitian matrices, which are the only matrices it is applied to; the paper does not print the explicit inverse (it cites Ref. [28]). The eigen-decomposition is taken as data $(U,\hat\lambda)$ in each statement, so every statement holds for every admissible choice of $U$. Unit vectors are expressed as $\sum_j|w_j|^2=1$. Division by $P_3$ or $P_2$ is written as multiplication by $1/P_3$ or $1/P_2$.
-- source:
--   J. J. Gil, On optimal filtering of measured Mueller matrices, arXiv:1605.04704v3 (2016), Section 2 (eqs. (2)-(4), (6)-(15)), Section 4 (eq. (23)), Section 5 (eqs. (24), (27)), PDF pp. 1-5

import Mathlib

/-!
J. J. Gil, *On optimal filtering of measured Mueller matrices*, arXiv:1605.04704v3 (2016):
the covariance (coherency) matrix of a Mueller matrix (Section 2, eqs. (2)-(4)), arbitrary and
spectral parallel decompositions (eqs. (6), (8), (13), (14)), the characteristic decomposition and
the indices of polarimetric purity (eqs. (9)-(11), (15)), the covariance filtering of a measured
Mueller matrix (Section 4, eq. (23)) and the noise-filtered matrices of Section 5 (eqs. (24), (27)).
-/

noncomputable section

namespace Arxiv1605_04704

open Matrix

/-- Eq. (2), PDF p. 1: the covariance (coherency) matrix `H(M)` of a real `4 × 4` matrix `M`
(indices `0..3` as in the paper, `m_kl = M k l`). -/
def cohMat (M : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 4 : ℂ) • !![
    Complex.mk (M 0 0 + M 0 1 + M 1 0 + M 1 1) 0,
    Complex.mk (M 0 2 + M 1 2) (M 0 3 + M 1 3),
    Complex.mk (M 2 0 + M 2 1) (-(M 3 0 + M 3 1)),
    Complex.mk (M 2 2 + M 3 3) (M 2 3 - M 3 2);
    Complex.mk (M 0 2 + M 1 2) (-(M 0 3 + M 1 3)),
    Complex.mk (M 0 0 - M 0 1 + M 1 0 - M 1 1) 0,
    Complex.mk (M 2 2 - M 3 3) (-(M 2 3 + M 3 2)),
    Complex.mk (M 2 0 - M 2 1) (-(M 3 0 - M 3 1));
    Complex.mk (M 2 0 + M 2 1) (M 3 0 + M 3 1),
    Complex.mk (M 2 2 - M 3 3) (M 2 3 + M 3 2),
    Complex.mk (M 0 0 + M 0 1 - M 1 0 - M 1 1) 0,
    Complex.mk (M 0 2 - M 1 2) (M 0 3 - M 1 3);
    Complex.mk (M 2 2 + M 3 3) (-(M 2 3 - M 3 2)),
    Complex.mk (M 2 0 - M 2 1) (M 3 0 - M 3 1),
    Complex.mk (M 0 2 - M 1 2) (-(M 0 3 - M 1 3)),
    Complex.mk (M 0 0 - M 0 1 - M 1 0 + M 1 1) 0]

/-- Section 2 ("Due to the biunivocal relation between H and M", PDF p. 2) and Section 4, step 5
(`M_cov = M(H_cov)`, PDF p. 4): the real `4 × 4` matrix `M(H)` whose covariance matrix is `H`.
Eq. (2) is a linear bijection from real `4 × 4` matrices onto `4 × 4` Hermitian matrices, so this
is its inverse on Hermitian matrices (the paper refers to Ref. [28] for the explicit formula). -/
def muellerOf (H : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Function.invFun cohMat H

/-- Eqs. (3)-(4), PDF pp. 1-2: `U` is a unitary matrix and `l = (λ̂₀, λ̂₁, λ̂₂, λ̂₃)` are the
normalized eigenvalues of `H(M)`, taken in decreasing order, with
`H(M) = m₀₀ U diag(λ̂₀, λ̂₁, λ̂₂, λ̂₃) U†` (`m₀₀ = M 0 0`). The columns `u_i` of `U` are the
eigenvectors. -/
def IsSpectralData (M : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ)
    (l : Fin 4 → ℝ) : Prop :=
  Antitone l ∧
    cohMat M = ((M 0 0 : ℝ) : ℂ) •
      ((U : Matrix (Fin 4) (Fin 4) ℂ) * Matrix.diagonal (fun i => (l i : ℂ)) *
        star (U : Matrix (Fin 4) (Fin 4) ℂ))

/-- Eq. (6) (and its Mueller form (13)), PDF p. 2: a parallel decomposition of `M` into `n` pure
components, `H(M) = ∑ᵢ pᵢ m₀₀ (wᵢ ⊗ wᵢ†)` with nonnegative coefficients summing to one and
linearly independent unit covariance vectors `wᵢ` in `Range H(M)`. -/
def IsPureDecomp (M : Matrix (Fin 4) (Fin 4) ℝ) (n : ℕ) (p : Fin n → ℝ)
    (w : Fin n → Fin 4 → ℂ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧ (∀ i, ∑ j, Complex.normSq (w i j) = 1) ∧
    (∀ i, w i ∈ LinearMap.range (Matrix.mulVecLin (cohMat M))) ∧ LinearIndependent ℂ w ∧
    cohMat M = ∑ i, ((p i * M 0 0 : ℝ) : ℂ) • Matrix.vecMulVec (w i) (star (w i))

/-- Eqs. (6)-(7) and (13), PDF p. 2: an arbitrary decomposition of `M` is a pure parallel
decomposition with exactly `r = rank H(M)` components. -/
abbrev IsArbitraryDecomp (M : Matrix (Fin 4) (Fin 4) ℝ) (p : Fin (cohMat M).rank → ℝ)
    (w : Fin (cohMat M).rank → Fin 4 → ℂ) : Prop :=
  IsPureDecomp M (cohMat M).rank p w

/-- Eqs. (8), (14), PDF p. 2: the `i`-th spectral component `M_Ui = m₀₀ M̂_Ui`, the Mueller matrix
with covariance matrix `H_Ui = m₀₀ (uᵢ ⊗ uᵢ†)`, `uᵢ` the `i`-th column of `U` (`c = m₀₀`). -/
def specComp (U : Matrix.unitaryGroup (Fin 4) ℂ) (c : ℝ) (i : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  muellerOf (((c : ℝ) : ℂ) • Matrix.vecMulVec (fun a => (U : Matrix (Fin 4) (Fin 4) ℂ) a i)
    (star (fun a => (U : Matrix (Fin 4) (Fin 4) ℂ) a i)))

/-- Eqs. (10), (15), PDF p. 2-3: the 2D depolarizer `M_2`, with covariance matrix
`H_2 = (1/2) m₀₀ U diag(1,1,0,0) U†` (`c = m₀₀`). -/
def depol2 (U : Matrix.unitaryGroup (Fin 4) ℂ) (c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  muellerOf (((c / 2 : ℝ) : ℂ) • ((U : Matrix (Fin 4) (Fin 4) ℂ) *
    Matrix.diagonal ![(1 : ℂ), 1, 0, 0] * star (U : Matrix (Fin 4) (Fin 4) ℂ)))

/-- Eqs. (10), (15), PDF p. 2-3: the 3D depolarizer `M_3`, with covariance matrix
`H_3 = (1/3) m₀₀ U diag(1,1,1,0) U†` (`c = m₀₀`). -/
def depol3 (U : Matrix.unitaryGroup (Fin 4) ℂ) (c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  muellerOf (((c / 3 : ℝ) : ℂ) • ((U : Matrix (Fin 4) (Fin 4) ℂ) *
    Matrix.diagonal ![(1 : ℂ), 1, 1, 0] * star (U : Matrix (Fin 4) (Fin 4) ℂ)))

/-- Eq. (15) and the list after it, PDF p. 3: the ideal depolarizer `M_Δ0 = m₀₀ diag(1,0,0,0)`
(`c = m₀₀`); its covariance matrix is `H_Δ0 = (1/4) m₀₀ I₄` (eq. (10)). -/
def idealDepol (c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  c • Matrix.diagonal ![(1 : ℝ), 0, 0, 0]

/-- Eq. (11), PDF p. 2: first index of polarimetric purity `P₁ = λ̂₀ - λ̂₁`. -/
def ipp1 (l : Fin 4 → ℝ) : ℝ := l 0 - l 1

/-- Eq. (11), PDF p. 2: second index of polarimetric purity `P₂ = λ̂₀ + λ̂₁ - 2λ̂₂`. -/
def ipp2 (l : Fin 4 → ℝ) : ℝ := l 0 + l 1 - 2 * l 2

/-- Eq. (11), PDF p. 2: third index of polarimetric purity `P₃ = λ̂₀ + λ̂₁ + λ̂₂ - 3λ̂₃`. -/
def ipp3 (l : Fin 4 → ℝ) : ℝ := l 0 + l 1 + l 2 - 3 * l 3

/-- Section 4, steps 1-2, PDF p. 4: `U` is a unitary matrix whose columns are orthonormal
eigenvectors of the Hermitian matrix `H_exp = H(M_exp)`, with eigenvalues `λ_exp,i = lam i` in
decreasing order: `H_exp = U diag(λ_exp,0, …, λ_exp,3) U†`. -/
def IsCovFilterData (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ)
    (lam : Fin 4 → ℝ) : Prop :=
  Antitone lam ∧
    cohMat Mexp = (U : Matrix (Fin 4) (Fin 4) ℂ) * Matrix.diagonal (fun i => (lam i : ℂ)) *
      star (U : Matrix (Fin 4) (Fin 4) ℂ)

/-- Section 4, step 3, PDF p. 4: the covariance-filtered eigenvalues `λ_cov,i`, obtained by
replacing every negative `λ_exp,i` by zero. -/
def covEig (lam : Fin 4 → ℝ) (i : Fin 4) : ℝ := max (lam i) 0

/-- Section 4, step 4, eq. (23), PDF p. 4: `H_cov = U diag(λ_cov,0, …, λ_cov,3) U†`. -/
def covH (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (U : Matrix (Fin 4) (Fin 4) ℂ) * Matrix.diagonal (fun i => (covEig lam i : ℂ)) *
    star (U : Matrix (Fin 4) (Fin 4) ℂ)

/-- Section 4, step 5, PDF p. 4: the covariance-filtered Mueller matrix `M_cov = M(H_cov)`. -/
def covMueller (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  muellerOf (covH U lam)

/-- Eq. (4) applied to `H_cov`, PDF pp. 2, 4: the normalized eigenvalues
`λ̂_i = λ_cov,i / tr H_cov` of `M_cov`, in decreasing order. -/
def covLhat (lam : Fin 4 → ℝ) (i : Fin 4) : ℝ := covEig lam i / ∑ j, covEig lam j

/-- Section 5, case b.1, eq. (24), PDF p. 4: the noise-filtered matrix
`M_f = [M_cov - (1 - P₃) M_Δ0] / P₃`, with `P_i` the indices of polarimetric purity of `M_cov`
and `M_Δ0` built with the `m₀₀` of `M_cov`. -/
def filt3 (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / ipp3 (covLhat lam)) •
    (covMueller U lam - (1 - ipp3 (covLhat lam)) • idealDepol (covMueller U lam 0 0))

/-- Section 5, case c.1, eq. (27), PDF p. 5: the noise-filtered matrix
`M_f = [M_cov - (1 - P₃) M_Δ0 - (P₃ - P₂) M_3] / P₂`, with `P_i`, `M_Δ0` and `M_3` those of
`M_cov`. -/
def filt2 (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / ipp2 (covLhat lam)) •
    (covMueller U lam - (1 - ipp3 (covLhat lam)) • idealDepol (covMueller U lam 0 0) -
      (ipp3 (covLhat lam) - ipp2 (covLhat lam)) • depol3 U (covMueller U lam 0 0))

end Arxiv1605_04704


