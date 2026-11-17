-- Prove2me | Definitions.Def_PFRelease_Supplement_phiLam
-- name    : PFRelease_Supplement_phiLam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:42:56.58547+00:00
-- url     : https://prove2.me/theorems/669e44f9-ebb6-4a60-b93a-e81d3b993c21
-- title:
--   Regularized second moment $\widehat\Sigma_\lambda(s)$, pseudoinverse, leverage $\mathcal L_\lambda(s,x)$ and the score $\varphi_\lambda$
-- statement:
--   Let $s$ be a nonempty dataset of vectors in $\mathbb R^d$, with null records represented by zero vectors and counted in $|s|$. Its Gram matrix is $s^Ts=\sum_{\text{slots}}x x^T$ and its **regularized second moment** is
--   $$
--   \widehat\Sigma_\lambda(s):=\frac{s^Ts}{|s|}+\lambda I_d\qquad(\lambda\ge0).
--   $$
--   For a real square matrix $A$, $A^\dagger$ is its Moore–Penrose pseudoinverse.
--
--   The **$\lambda$-regularized leverage** of $x\in\mathbb R^d$ with respect to $s$ is $\mathcal L_\lambda(s,x):=x^T\widehat\Sigma_\lambda(s)^{-1}x$ for $\lambda>0$, and for $\lambda=0$ its limit as $\lambda\to0^+$:
--   $$
--   \mathcal L_0(s,x)=\begin{cases}x^T\widehat\Sigma_0(s)^\dagger x=|s|\,x^T\mathbf L_s^\dagger x,& x\in\operatorname{range}(\mathbf L_s),\\ \infty,& \text{otherwise,}\end{cases}
--   $$
--   where $\mathbf L_s=s^Ts$. The friendliness score is $\varphi_\lambda(s,x):=1/\mathcal L_\lambda(s,x)$, with $1/0:=\infty$, $1/\infty:=0$, and $\varphi_\lambda(\emptyset,x):=0$.
--
--   The score measures how well a record is explained by the reference data: it is large when $x$ lies in a thin ellipsoid shaped like the data, and it is the score of the Gaussian sketches (§5.2) and, with zero ridge, of the effective-resistance mechanism (§5.4).
--
--   **Formalization Note** Records are `Option (EuclideanSpace ℝ ι)` (`none` is $\perp$). The pseudoinverse is the matrix of the published Moore–Penrose pseudoinverse `HarmonicGames.Decomposition.pinv` of the map $x\mapsto Ax$ on Euclidean space. Leverages and scores take values in $[0,\infty]$ (`ℝ≥0∞`). The value of $\varphi_\lambda$ at the null record is not fixed by the paper; it is set to $0$, and the theorems that use the score have inputs without null records. The definition is intended for $\lambda\ge0$.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Definition D.7, p.41 (PDF p.43); eq. (2), p.17 (PDF p.19); §D.4, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_PFRelease_Dataset
import Definitions.Def_HarmonicGames_Decomposition_Pinv

open Matrix

namespace PFRelease.Supplement

/-- The vector of a record of `ℝ^ι`, with the null record `⊥` represented by the zero vector
(Shenfeld, Tsfadia, Ligett, arXiv:2610.40654, held version sha256 e1d516b3…, Definition D.7, p.41 =
PDF p.43: "with null records represented by zero vectors"). -/
def recVec {ι : Type*} : Option (EuclideanSpace ℝ ι) → (ι → ℝ)
  | none => 0
  | some x => WithLp.ofLp x

/-- The Gram matrix `sᵀs = Σ_{slots} x xᵀ` of a dataset of vectors (Definition D.7, p.41; §D.4, p.50,
where it is the Laplacian `L_s = Σ_{e∈s} x_e x_eᵀ` of a dataset of edge records); null records
contribute zero and are still counted in `|s|`. -/
noncomputable def gram {ι : Type*} [Fintype ι] (l : List (Option (EuclideanSpace ℝ ι))) :
    Matrix ι ι ℝ :=
  (l.map fun x => vecMulVec (recVec x) (recVec x)).sum

/-- The regularized second moment `Σ̂_λ(s) := sᵀs/|s| + λ I_d` of a nonempty dataset of vectors
(Definition D.7, p.41 = PDF p.43). -/
noncomputable def secondMoment {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ℝ)
    (l : List (Option (EuclideanSpace ℝ ι))) : Matrix ι ι ℝ :=
  (l.length : ℝ)⁻¹ • gram l + lam • (1 : Matrix ι ι ℝ)

/-- The Moore–Penrose pseudoinverse `A†` of a real square matrix (§5.4, p.20; §D.4, p.50): the matrix of
the published Moore–Penrose pseudoinverse `HarmonicGames.Decomposition.pinv` of the linear map
`x ↦ A x` on the Euclidean space `ℝ^ι`.

**Formalization Note** `Matrix.toEuclideanLin` identifies matrices with linear maps of `EuclideanSpace ℝ ι`
(standard inner product), so `A†` is the usual matrix pseudoinverse; for a symmetric
`A = Q diag(μ) Qᵀ` it is `Q diag(μ†) Qᵀ` with `μ† = 1/μ` for `μ ≠ 0` and `0† = 0`. -/
noncomputable def pinv {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  Matrix.toEuclideanLin.symm (HarmonicGames.Decomposition.pinv (Matrix.toEuclideanLin A))

open Classical in
/-- The `λ`-regularized leverage `L_λ(s, x)` of a vector `x` with respect to a nonempty dataset `s`
(Definition D.7, p.41 = PDF p.43; the zero-ridge formula of §D.4, p.50 = PDF p.52):
`L_λ(s, x) := xᵀ Σ̂_λ(s)⁻¹ x` for `λ > 0`, and for `λ = 0` its limit as `λ → 0⁺`, which is
`xᵀ Σ̂_0(s)† x` if `x ∈ range(Σ̂_0(s))` and `∞` otherwise.

**Formalization Note** Values in `[0, ∞]`. For `λ = 0`, `Σ̂_0(s) = L_s/|s|`, so the finite branch is
`|s| xᵀ L_s† x` and the range is `range(L_s)`, exactly the display on p.50. The definition is intended
for `λ ≥ 0`; for `λ < 0` it returns the zero-ridge value (never used). -/
noncomputable def leverage {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ℝ)
    (l : List (Option (EuclideanSpace ℝ ι))) (x : EuclideanSpace ℝ ι) : ENNReal :=
  if 0 < lam then
    ENNReal.ofReal (WithLp.ofLp x ⬝ᵥ ((secondMoment lam l)⁻¹ *ᵥ WithLp.ofLp x))
  else if WithLp.ofLp x ∈ LinearMap.range (Matrix.toLin' (secondMoment 0 l)) then
    ENNReal.ofReal (WithLp.ofLp x ⬝ᵥ (pinv (secondMoment 0 l) *ᵥ WithLp.ofLp x))
  else ⊤

/-- The friendliness score `φ_λ(s, x) := 1/L_λ(s, x)` (Definition D.7, p.41 = PDF p.43; eq. (2),
p.17; with `λ = 0` the score `φ_0` of eq. (4), p.20), with `1/0 := ∞` and `1/∞ := 0`, and
`φ_λ(∅, x) := 0` (Definition 4.4).

**Formalization Note** `ENNReal` inversion gives `1/0 = ∞` and `1/∞ = 0`. The value at the null
record `⊥` (`none`) is unrestricted by the paper (footnote 5, p.12); it is set to `0` here and
never matters for the theorems, whose inputs have no null records. -/
noncomputable def phiLam {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ℝ) :
    List (Option (EuclideanSpace ℝ ι)) → Option (EuclideanSpace ℝ ι) → ENNReal
  | [], _ => 0
  | _ :: _, none => 0
  | y :: l, some x => (leverage lam (y :: l) x)⁻¹

end PFRelease.Supplement


