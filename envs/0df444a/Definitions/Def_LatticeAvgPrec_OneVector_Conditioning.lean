-- Prove2me | Definitions.Def_LatticeAvgPrec_OneVector_Conditioning
-- name    : LatticeAvgPrec_OneVector_Conditioning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:44:37.26941+00:00
-- url     : https://prove2.me/theorems/fec7d362-240d-4e0d-bff2-ddb9ab2d7f8a
-- title:
--   Spectral and Frobenius norms, $Y^\dagger$, $\kappa_{\rm col}$, positive QR and unitriangular matrices
-- statement:
--   For a real matrix $M$, $\|M\|_2$ is the spectral norm (the $\ell_2$ operator norm, §2 p.8) and $\|M\|_F$ the Frobenius norm (App. A, p.27). For $Y$ of full column rank, $Y^\dagger=(Y^TY)^{-1}Y^T$ and $\kappa_2(Y)=\|Y\|_2\|Y^\dagger\|_2$. The column-scaled condition number (Definition 4.3, p.15) is
--   $$\kappa_{\rm col}(Y)=\inf_{\Delta>0\ \text{diagonal}}\kappa_2(Y\Delta).$$
--   A positive (thin) QR factorization of $X\in\mathbb R^{d\times k}$ is $X=OR$ with $O^TO=I$ and $R$ square upper triangular with positive diagonal; its diagonal entries are the Gram–Schmidt lengths of $X$. Writing $R=\Delta W$ with $\Delta=\operatorname{diag}(R_{ii})$, $W$ is the unitriangular factor ($W_{ij}=R_{ij}/R_{ii}$). A matrix is upper unitriangular if it is upper triangular with unit diagonal (App. A, p.27).
--
--   These objects state the numerical interface of Lemma 4.4 and Lemmas A.1–A.2.
--
--   **Formalization Note** The spectral norm is the least $c\ge0$ with $\|Mx\|_2\le c\|x\|_2$ for all $x$, an attained infimum. $\kappa_{\rm col}$ is an infimum over positive diagonal scalings, a nonempty set of nonnegative reals.
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), §2 p.8 (‖·‖₂); Definition 4.3 p.15; App. A p.27 (Frobenius norm, positive QR, unitriangular)

import Definitions.Def_LatticeAvgPrec_OneVector_Lattice
open Matrix

namespace LatticeAvgPrec.OneVector

/-- Spectral norm (`ℓ₂` operator norm) `‖M‖₂` of a real matrix: the least `c ≥ 0` with
`‖Mx‖₂ ≤ c‖x‖₂` for all `x`. -/
noncomputable def specNorm {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ ∀ x : Fin b → ℝ, l2 (M *ᵥ x) ≤ c * l2 x}

/-- Frobenius norm `‖M‖_F`. -/
noncomputable def frob {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- `Y^† = (YᵀY)⁻¹Yᵀ` (Definition 4.3, p.15). -/
noncomputable def pinv {a b : ℕ} (Y : Matrix (Fin a) (Fin b) ℝ) : Matrix (Fin b) (Fin a) ℝ :=
  (Yᵀ * Y)⁻¹ * Yᵀ

/-- `κ₂(Y) = ‖Y‖₂ ‖Y^†‖₂`. -/
noncomputable def kappa2 {a b : ℕ} (Y : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  specNorm Y * specNorm (pinv Y)

/-- Column-scaled condition number (Definition 4.3, p.15):
`κ_col(Y) = inf_{Δ > 0 diagonal} κ₂(YΔ)`. -/
noncomputable def kappaCol {a b : ℕ} (Y : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  sInf ((fun δ : Fin b → ℝ => kappa2 (Y * Matrix.diagonal δ)) '' {δ | ∀ i, 0 < δ i})

/-- Upper triangular with unit diagonal (unitriangular, App. A, p.27). -/
def IsUpperUnitri {R : Type*} [Zero R] [One R] {k : ℕ} (M : Matrix (Fin k) (Fin k) R) : Prop :=
  (∀ i j, j < i → M i j = 0) ∧ ∀ i, M i i = 1

/-- Positive (thin) QR factorization (App. A, p.27): `X = O R` with `OᵀO = I` and `R` square upper
triangular with positive diagonal. Its diagonal entries are the Gram–Schmidt lengths of `X`. -/
def IsPosQR {d k : ℕ} (X : Matrix (Fin d) (Fin k) ℝ) (O : Matrix (Fin d) (Fin k) ℝ)
    (R : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  X = O * R ∧ Oᵀ * O = 1 ∧ (∀ i j, j < i → R i j = 0) ∧ ∀ i, 0 < R i i

/-- The unitriangular factor `W` of `R = ΔW`, `Δ = diag(R_ii)`. -/
noncomputable def unitFactor {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => R i j / R i i

end LatticeAvgPrec.OneVector


