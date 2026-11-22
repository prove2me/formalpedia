-- Prove2me | Definitions.Def_SKHessianAscent_Resolvent
-- name    : SKHessianAscent_Resolvent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-22T19:55:51.679933+00:00
-- url     : https://prove2.me/theorems/835e1ba4-5226-40d0-9a05-08e8bc817ab7
-- title:
--   The resolvents $Q(m)$, $\widehat Q(m)$ of (6.1), the diagonal error $\delta_{\mathrm{diag}}(m)$ of (6.8), and complex matrix norms
-- statement:
--   For $m\in(-1,1)^n$, with $D(m)=\mathrm{diag}(1/(1-m_i^2))$:
--
--   - `aTap β m` is $a(m)=\beta^2\,\mathrm{tr}_n(D(m)^{-1})$;
--   - `Qres β A m` is the resolvent without the rank-one term,
--   $$Q(m)=\big(a(m)I_n-\beta A+D(m)\big)^{-1};$$
--   - `deltaDiag β A m` is
--   $$\delta_{\mathrm{diag}}(m)=\mathbf E_{\mathcal D_n}\big[\widehat Q(m)^2\big]D(m)^2-\big(1+\beta^2\mathrm{tr}_n(\widehat Q(m)^2)\big)I_n,$$
--   and `deltaDiagRes β A m` is the same expression with $\widehat Q$ replaced by $Q$.
--
--   For complex matrices, `cOpNorm` is the Euclidean operator norm, `cSchatten2` is the normalized Schatten 2-norm $\|M\|_{L^2}=\big(\tfrac1n\sum_{i,j}|M_{ij}|^2\big)^{1/2}$, and `toC` embeds a real matrix into the complex matrices.
--
--   These are the objects of the resolvent estimates of Section 6 and Appendix A.
--
--   **Formalization Note** $\widehat Q(m)=\big(a(m)I_n-\beta A+D(m)-\tfrac{2\beta^2}{n}mm^{\mathsf T}\big)^{-1}$ is `Qhat` of `SKHessianAscent_Model`; for $n\ge1$ its argument is the TAP Hessian (2.2), since $\mathrm{tr}_n(D(m)^{-1})=1-\|m\|_2^2/n$. Inverses are Mathlib's matrix inverse ($0$ for a singular matrix).
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §6, equations (6.1) p. 36 and (6.8) p. 38; Appendix A.1, p. 45

import Mathlib
import Definitions.Def_SKHessianAscent_Model

open scoped BigOperators

namespace SKHessianAscent

/-!
# Resolvents of Section 6 and complex matrix norms of Appendix A

H. Lee, J. S. Sandhu, J. Shi, *Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick
model at β < 1*, §6, equations (6.1) and (6.8) (pp. 36, 38); Appendix A.1 (p. 45).

**Formalization Note.** `Qres` is the resolvent `Q(m)` of (6.1), without the rank-one term of the
TAP Hessian; `Qhat` (in `SKHessianAscent_Model`) is `Q̂(m)`, with it. For `n ≥ 1`,
`tapHess β A m = aTap β m • 1 − β • A + Dmat m − (2β²/n) m mᵀ`. The complex norms are the
Euclidean operator norm and the normalized Schatten 2-norm `‖X‖_{L²} = (tr_n(X X*))^{1/2}` of
arXiv:2605.03718, §1.6.
-/

noncomputable section

/-- `a(m) = β² tr_n(D(m)⁻¹)` (6.1). -/
def aTap {n : ℕ} (β : ℝ) (m : Fin n → ℝ) : ℝ := β ^ 2 * ntr (Dinv m)

/-- `Q(m) = (a(m) I_n − βA + D(m))⁻¹` (6.1). -/
def Qres {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (aTap β m • (1 : Matrix (Fin n) (Fin n) ℝ) - β • A + Dmat m)⁻¹

/-- `δ_diag(m) = E_{D_n}[Q̂(m)²] D(m)² − (1 + β² tr_n(Q̂(m)²)) I_n` (6.8). -/
def deltaDiag {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  diagPart (Qhat β A m ^ 2) * Dmat m ^ 2
    - (1 + β ^ 2 * ntr (Qhat β A m ^ 2)) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- (6.8) with `Q̂` replaced by `Q`: `E_{D_n}[Q(m)²] D(m)² − (1 + β² tr_n(Q(m)²)) I_n`. -/
def deltaDiagRes {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  diagPart (Qres β A m ^ 2) * Dmat m ^ 2
    - (1 + β ^ 2 * ntr (Qres β A m ^ 2)) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- The Euclidean operator norm of a complex `n × n` matrix. -/
def cOpNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖

/-- The normalized Schatten 2-norm `‖M‖_{L²} = ((1/n) ∑_{i,j} |M_ij|²)^{1/2}` of a complex
matrix. -/
def cSchatten2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt ((∑ i, ∑ j, ‖M i j‖ ^ 2) / n)

/-- A real matrix as a complex matrix. -/
def toC {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  M.map (algebraMap ℝ ℂ)

end

end SKHessianAscent


