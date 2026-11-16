-- Prove2me | Definitions.Def_CliffordCert_Optimal_Supplement_support_model
-- name    : CliffordCert_Optimal_Supplement_support_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:37:44.726657+00:00
-- url     : https://prove2.me/theorems/77581107-5a95-4431-875a-363391fe0f12
-- title:
--   Support coordinates and the reference-preserving channel
-- statement:
--   Let $\sigma$ be a density matrix on a finite complex coordinate space, and let $J:\mathbb C^k\to\mathbb C^d$ have orthonormal columns spanning exactly the range of $\sigma$. Set $P=JJ^\dagger$, $Q=I-P$ and $\sigma_s=J^\dagger\sigma J$. For a state $\rho$ define $p=\operatorname{Tr}(Q\rho)$ and, when $p<1$, its normalized compression $\rho_P=(1-p)^{-1}P\rho P$. The concrete complex-linear support map is
--
--   $$
--   \Gamma_\sigma(X)=J^\dagger XJ+\operatorname{Tr}(QX)\sigma_s.
--   $$
--
--   The file also defines matrix conjugation $X\mapsto AXA^\dagger$, orthogonal projections (Hermitian idempotents), and the uniform reference $P/k$. The support projection is computed from $J$; range equality ensures that a larger subspace cannot be substituted for the reference's support. Channel validity and every norm or testing guarantee are left for theorem items. These objects supply the support reduction of Lemma 12 and the fixed reference of Theorem 6.
--
--   **Formalization Note** Matrices use zero-based finite coordinates. Rank is complex rank, traces used as probabilities take their real part, and all trace norms are full, unhalved Schatten 1 norms. The support map is defined on all operators by its matrix-unit coefficients, including the coefficient $Q_{ba}$ multiplying $X_{ab}$ in the trace. The normalization is used only under $p<1$, and $P/k$ only for positive $k$.
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), pp. 17–18 (PDF 18–19), §F.1, Eqs. (29)–(30); pp. 7–8 (PDF 8–9), Theorem 6; source.pdf SHA256 2199cc2ec4c0cc01bfa75380982fe283d38a544dcae40abe5a37198f1a088114

import Definitions.Def_CliffordCert_Optimal_matrix_model
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal.Supplement

/-- Orthogonal projection, without any restriction on its rank. -/
def IsOrthogonalProjection {I : Type} [Fintype I] (P : Mat I) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- A choice of orthonormal coordinates for the actual range of the reference.
    These are geometric conditions only, with no channel or norm guarantees. -/
def IsSupportCoordinates {I : Type} [Fintype I] {k : ℕ}
    (σ : Mat I) (J : Matrix I (Fin k) ℂ) : Prop :=
  Jᴴ * J = 1 ∧ LinearMap.range J.mulVecLin = LinearMap.range σ.mulVecLin

def supportProjection {I : Type} [Fintype I] {k : ℕ}
    (J : Matrix I (Fin k) ℂ) : Mat I := J * Jᴴ

def supportReference {I : Type} [Fintype I] {k : ℕ}
    (σ : Mat I) (J : Matrix I (Fin k) ℂ) : Mat (Fin k) := Jᴴ * σ * J

/-- The real leakage probability; the trace is real on states and projections. -/
def leakage {I : Type} [Fintype I] [DecidableEq I] (P ρ : Mat I) : ℝ :=
  (Matrix.trace ((1 - P) * ρ)).re

/-- Eq. (29). Used only when leakage is strictly below one. -/
def normalizedCompression {I : Type} [Fintype I] [DecidableEq I]
    (P ρ : Mat I) : Mat I := ((1 - leakage P ρ : ℝ)⁻¹ : ℂ) • (P * ρ * P)

/-- Matrix conjugation, as a complex-linear map on all operators. -/
def conjugation {I O : Type} [Fintype I] (A : Matrix O I ℂ) : Mat I →ₗ[ℂ] Mat O :=
  fromCoefficients fun u v a b => A u a * star (A v b)

/-- Eq. (30) on ALL matrices, in matrix-unit coefficients:
    Γσ(X) = J† X J + Tr((I-JJ†)X) (J† σ J).
    In the trace term the coefficient of X[a,b] is Q[b,a]. -/
def supportChannel {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}
    (σ : Mat I) (J : Matrix I (Fin k) ℂ) : Mat I →ₗ[ℂ] Mat (Fin k) :=
  fromCoefficients fun u v a b =>
    star (J a u) * J b v + (1 - supportProjection J) b a * supportReference σ J u v

/-- The fixed-reference state P/k in Theorem 6. -/
def uniformSupport {I : Type} [DecidableEq I] (P : Mat I) (k : ℕ) : Mat I :=
  (k : ℂ)⁻¹ • P

end CliffordCert.Optimal.Supplement


