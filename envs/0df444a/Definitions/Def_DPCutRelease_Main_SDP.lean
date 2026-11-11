-- Prove2me | Definitions.Def_DPCutRelease_Main_SDP
-- name    : DPCutRelease_Main_SDP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:11:34.924213+00:00
-- url     : https://prove2.me/theorems/04b2965c-8f80-475e-935b-75dcf14e430a
-- title:
--   The elliptope 𝒳, q(X), the log-det regularized objective F(D) and its maximizer X_D, N(0, X) and the Gaussian estimator ĝ (Eqs. (3)–(4), (7))
-- statement:
--   **Feasible region (Eq. (3)).** $\mathcal X=\{X\in\mathbb R^{n\times n}: X=X^\top,\ \mathrm{diag}(X)=\mathbf 1_n,\ X\succeq \tfrac1n I_n\}$. For $X\in\mathcal X$ and $e=\{u,v\}$, $q_e(X)=\frac{1-X_{uv}}2\in[0,1]$, the fraction of $e$ cut by $X$.
--
--   **Objective (Eqs. (4), (7)).** With $b_e=e_u-e_v$, $A_D=\frac14\sum_e D_e b_eb_e^\top$, so that $\langle A_D,X\rangle=\operatorname{tr}(A_D^\top X)=\langle D,q(X)\rangle$. For $\lambda>0$ and any matrix $A$, $\arg\max_{X\in\mathcal X}\{\langle A,X\rangle+\lambda\log\det X\}$ exists and is unique ($\mathcal X$ is compact and the objective is continuous and strictly concave on it); $X_D$ is this maximizer for $A=A_D$, and
--   $$F(D)=\max_{X\in\mathcal X}\{\langle D,q(X)\rangle+\lambda\log\det X\}.$$
--
--   **Gaussians.** $N(0,X)$ is the law of $X^{1/2}Z$, $Z\sim N(0,I_n)$ (Mathlib's `multivariateGaussian 0 X`); for $X\succ0$ its density is $\mathrm{pdf}_X(z)=(2\pi)^{-n/2}\det(X)^{-1/2}e^{-z^\top X^{-1}z/2}$. $X^{-1/2}=(X^{1/2})^{-1}$, $\|M\|_F=(\sum_{ij}M_{ij}^2)^{1/2}$, and $E=X_0^{-1/2}(X_1-X_0)X_1^{-1/2}$.
--
--   **Estimator (Algorithm 2 line 8).** For a batch $Z^{(1)},\dots,Z^{(k)}$, $g(u,v)=\frac1k\sum_{j=1}^k\frac{(Z^{(j)}_u-Z^{(j)}_v)^2}4$ and $\hat g(u,v)=\min\{g(u,v)/2,1\}$; the batch law is $N(0,X)^{\otimes k}$.
--
--   **Formalization Note.** `regArgmax lam A` is the unique maximizer when one exists (always, for $\lambda>0$) and the junk value $I_n$ otherwise; `Freg lam D` is the objective at `XD lam D = regArgmax lam (AD D)`, i.e. the maximum. `edgeMat ξ` $=\sum_e\xi_eb_eb_e^\top/4$. `Real.log` is the natural logarithm with `log 0 = 0`; $X^{1/2}$ is `CFC.sqrt X`.
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 14, Eqs. (3)–(4); p. 19, Eq. (7); p. 15–16, Algorithm 2 lines 5–8; p. 21, Lemma 14

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace DPCutRelease.Main

/-!
# The log-det regularized SDP over the elliptope, `F(D)`, `N(0, X)` and the Gaussian estimator

Eliáš et al., arXiv:2611.06670v1, p. 14 (Eqs. (3)–(4)), p. 15 (Lemma 10, Algorithm 2 lines 7–8),
p. 19 (Eq. (7), Lemma 13), p. 21 (Lemma 14).

* `Elliptope n` is `𝒳 = {X ∈ ℝ^{n×n} : X = Xᵀ, diag(X) = 1_n, X ⪰ (1/n) I_n}` (Eq. (3)).
* `qe X e = q_{uv}(X) = (1 − X_{uv})/2` for `e = {u, v}`; `bvec e = e_u − e_v`;
  `AD D = (1/4) Σ_e D_e b_e b_eᵀ` (Eq. (7)); `frob A X = ⟨A, X⟩ = tr(Aᵀ X)`.
* `regObj lam A X = ⟨A, X⟩ + λ log det X`; `IsRegMaximizer lam A X`: `X ∈ 𝒳` maximizes it over `𝒳`.
  `regArgmax lam A` is the maximizer when it exists and is unique (for `λ > 0` it does: `𝒳` is
  compact, `log det` is continuous and strictly concave on it), and the junk value `I_n` otherwise.
  `X_D = regArgmax lam (AD D)` and `F(D) = regObj lam (AD D) X_D = max_{X∈𝒳} {⟨D, q(X)⟩ + λ log det X}`
  (Eq. (4)), using `⟨A_D, X⟩ = ⟨D, q(X)⟩`.
* `gaussLaw X = N(0, X)`: Mathlib's `multivariateGaussian 0 X`, the law of `X^{1/2} Z` with `Z`
  standard normal (`X^{1/2} = CFC.sqrt X`). `gaussPdf X z = (2π)^{−n/2} det(X)^{−1/2} e^{−zᵀX⁻¹z/2}`
  is its density for `X` positive definite. `invSqrt X = X^{−1/2} = (CFC.sqrt X)⁻¹`.
  `frobNorm M = ‖M‖_F = (Σ_{ij} M_{ij}²)^{1/2}`.
* `gEst Z e = (1/k) Σ_j (Z^{(j)}_u − Z^{(j)}_v)²/4` and `ghat Z e = min{gEst Z e / 2, 1}` for a batch
  `Z = (Z^{(1)}, …, Z^{(k)})` (Algorithm 2 line 8, Lemmas 10–11).
* `Real.log` is the natural logarithm (§2: "All logarithms in the paper are natural"), with Lean's
  totalization `log 0 = 0`, `log x = log |x|`; `1/n` is `0` at `n = 0`.
-/

/-- A real `n × n` matrix. -/
abbrev Mat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℝ

/-- Eq. (3): the feasible region `𝒳 = {X : X = Xᵀ, diag(X) = 1, X ⪰ (1/n) I}`. -/
def Elliptope (n : ℕ) : Set (Mat n) :=
  {X | X.IsHermitian ∧ (∀ i, X i i = 1) ∧ (X - ((1 : ℝ) / n) • (1 : Mat n)).PosSemidef}

/-- `q_{uv}(X) = (1 − X_{uv})/2`, the fraction of the pair `{u, v}` cut by `X`. -/
noncomputable def qe {n : ℕ} (X : Mat n) (e : Pair n) : ℝ := (1 - X e.1.1 e.1.2) / 2

/-- `q(X) = (q_e(X))_e`. -/
noncomputable def qvec {n : ℕ} (X : Mat n) : EdgeVec n := fun e => qe X e

/-- `b_e = e_u − e_v` for `e = {u, v}`. -/
def bvec {n : ℕ} (e : Pair n) : Fin n → ℝ := Pi.single e.1.1 1 - Pi.single e.1.2 1

/-- `Σ_e ξ_e b_e b_eᵀ / 4`. -/
noncomputable def edgeMat {n : ℕ} (ξ : EdgeVec n) : Mat n :=
  ∑ e, (ξ e / 4) • vecMulVec (bvec e) (bvec e)

/-- Eq. (7): `A_D = (1/4) Σ_e D_e b_e b_eᵀ`. -/
noncomputable def AD {n : ℕ} (D : EdgeVec n) : Mat n := edgeMat D

/-- The trace inner product `⟨A, X⟩ = tr(Aᵀ X)`. -/
def frob {n : ℕ} (A X : Mat n) : ℝ := (Aᵀ * X).trace

/-- The regularized objective `⟨A, X⟩ + λ log det X`. -/
noncomputable def regObj {n : ℕ} (lam : ℝ) (A X : Mat n) : ℝ := frob A X + lam * Real.log X.det

/-- `X` maximizes `⟨A, ·⟩ + λ log det` over `𝒳`. -/
def IsRegMaximizer {n : ℕ} (lam : ℝ) (A X : Mat n) : Prop :=
  X ∈ Elliptope n ∧ ∀ Y ∈ Elliptope n, regObj lam A Y ≤ regObj lam A X

open Classical in
/-- `arg max_{X ∈ 𝒳} {⟨A, X⟩ + λ log det X}`: the unique maximizer (it exists and is unique for
`λ > 0`); `I_n` if there is no unique maximizer (never the case for `λ > 0`). -/
noncomputable def regArgmax {n : ℕ} (lam : ℝ) (A : Mat n) : Mat n :=
  if h : ∃! X, IsRegMaximizer lam A X then h.exists.choose else 1

/-- `X_D`, the maximizer in Eq. (4). -/
noncomputable def XD {n : ℕ} (lam : ℝ) (D : EdgeVec n) : Mat n := regArgmax lam (AD D)

/-- Eq. (4): `F(D) = max_{X ∈ 𝒳} {⟨D, q(X)⟩ + λ log det X}`, the value at the maximizer `X_D`. -/
noncomputable def Freg {n : ℕ} (lam : ℝ) (D : EdgeVec n) : ℝ := regObj lam (AD D) (XD lam D)

/-- `N(0, X)` on `ℝⁿ`: Mathlib's multivariate Gaussian with mean `0` and covariance `X`. -/
noncomputable def gaussLaw {n : ℕ} (X : Mat n) : Measure (EuclideanSpace ℝ (Fin n)) :=
  multivariateGaussian 0 X

/-- The density of `N(0, X)` for positive definite `X`:
`(2π)^{−n/2} det(X)^{−1/2} exp(−zᵀ X⁻¹ z / 2)`. -/
noncomputable def gaussPdf {n : ℕ} (X : Mat n) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (Real.sqrt ((2 * Real.pi) ^ n * X.det))⁻¹ *
    Real.exp (-((fun i => z i) ⬝ᵥ (X⁻¹ *ᵥ fun i => z i)) / 2)

/-- `X^{−1/2}`: the inverse of the positive square root. -/
noncomputable def invSqrt {n : ℕ} (X : Mat n) : Mat n := (CFC.sqrt X)⁻¹

/-- The Frobenius norm `‖M‖_F`. -/
noncomputable def frobNorm {n : ℕ} (M : Mat n) : ℝ := Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- The relative error matrix `E = X₀^{−1/2} (X₁ − X₀) X₁^{−1/2}`. -/
noncomputable def relErr {n : ℕ} (X0 X1 : Mat n) : Mat n := invSqrt X0 * (X1 - X0) * invSqrt X1

/-- `g(u, v) = (1/k) Σ_{j=1}^k (Z^{(j)}_u − Z^{(j)}_v)² / 4` for a batch of `k` vectors. -/
noncomputable def gEst {n k : ℕ} (Z : Fin k → EuclideanSpace ℝ (Fin n)) (e : Pair n) : ℝ :=
  (1 / (k : ℝ)) * ∑ j, (Z j e.1.1 - Z j e.1.2) ^ 2 / 4

/-- `ĝ(u, v) = min{g(u, v)/2, 1}`. -/
noncomputable def ghat {n k : ℕ} (Z : Fin k → EuclideanSpace ℝ (Fin n)) : EdgeVec n :=
  fun e => min (gEst Z e / 2) 1

/-- The law of a batch `(Z^{(1)}, …, Z^{(k)})` of independent `N(0, X)` vectors. -/
noncomputable def batchLaw {n : ℕ} (k : ℕ) (X : Mat n) :
    Measure (Fin k → EuclideanSpace ℝ (Fin n)) :=
  Measure.pi fun _ => gaussLaw X

end DPCutRelease.Main


