-- Prove2me | Definitions.Def_PetzFisher_JMap
-- name    : PetzFisher_JMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:01.087589+00:00
-- url     : https://prove2.me/theorems/2a0e184b-2bc0-4463-8b84-3c7e02401246
-- title:
--   The linear mapping $\mathbb J^f_D = f(\mathbb L_D\mathbb R_D^{-1})\mathbb R_D$
-- statement:
--   Let $D\in M_n$ be a positive invertible matrix and $f:\mathbb R^+\to\mathbb R^+$. Write $\mathbb L_D(X)=DX$ and $\mathbb R_D(X)=XD$ for left and right multiplication by $D$ on $M_n$. The linear mapping $\mathbb J^f_D:M_n\to M_n$ is
--
--   $$
--   \mathbb J^f_D=f(\mathbb L_D\mathbb R_D^{-1})\,\mathbb R_D .
--   $$
--
--   Concretely, if $D=\sum_u u\,P_u$ is the spectral decomposition of $D$ over its distinct eigenvalues $u>0$, then $\mathbb L_D\mathbb R_D^{-1}$ acts on $P_uBP_v$ as multiplication by $u/v$ and $\mathbb R_D$ as multiplication by $v$, so
--
--   $$
--   \mathbb J^f_D B=\sum_{u,v} v\,f(u/v)\,P_u B P_v .
--   $$
--
--   For diagonal $D$ this is the Hadamard multiplication $(\mathbb J^f_D B)_{ij}=\lambda_j f(\lambda_i/\lambda_j)B_{ij}$. With $f$ a standard operator monotone function, $\mathbb J^f_D$ defines the generalized covariance, and its inverse the quantum Fisher information.
--
--   **Formalization Note** $M_n$ is the algebra of complex matrices indexed by a finite type. The definition is written in the spectral-projector form above, using the eigenvalue set and spectral projections of the published definition layer, term for term like the published inverse `inverseMetric` (with $(v f(u/v))^{-1}$ in place of $v f(u/v)$). Only values of $f$ on $(0,\infty)$ enter for positive definite $D$; for a non-Hermitian $D$ the eigenvalue set is empty and the value is $0$, so every statement assumes $D$ positive definite.
-- source:
--   Petz–Ghinea, Introduction to quantum Fisher information, arXiv:1008.2417v1, §1.2, p.7 (definition of 𝕁^f_D) and eq. (12), p.8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P31

open scoped Matrix ComplexOrder

namespace PetzFisher

/-- The linear mapping `𝕁^f_D = f(𝕃_D ℝ_D^{-1}) ℝ_D : Mₙ → Mₙ` (Petz–Ghinea, *Introduction to
quantum Fisher information*, arXiv:1008.2417v1, §1.2, p.7): "Let `D ∈ Mₙ` be a positive invertible
matrix. The linear mapping `𝕁^f_D : Mₙ → Mₙ` is defined by the formula `𝕁^f_D = f(𝕃_D ℝ_D^{-1}) ℝ_D`,
where `f : ℝ⁺ → ℝ⁺`, `𝕃_D(X) = DX` and `ℝ_D(X) = XD`."

**Formalization Note.** `Mₙ` is `Matrix I I ℂ` for a finite index type `I`. The functional calculus
of the commuting pair `𝕃_D`, `ℝ_D` is written in spectral-projector form: with `P_u` the spectral
projection of `D` for its distinct eigenvalue `u` (`Support50.P12.spec`, `QAlgorithms.spectralProjector`),
the operators `B ↦ P_u B P_v` decompose `Mₙ`, and on their ranges `𝕃_D ℝ_D^{-1}` acts as `u / v`
and `ℝ_D` as `v`. Hence `𝕁^f_D B = Σ_{u,v} v f(u/v) P_u B P_v`, the same form as the published
inverse `Bridge50.P31.inverseMetric` (with `(v f(u/v))^{-1}` there). Only the values of `f` on
`(0, ∞)` enter when `D` is positive definite. For a non-Hermitian `D` the spectrum `spec D` is empty
and the value is `0`; every statement of this mission assumes `D` positive definite. -/
noncomputable def JMap {I : Type} [Fintype I] [DecidableEq I] (f : ℝ → ℝ) (D B : Matrix I I ℂ) :
    Matrix I I ℂ :=
  ∑ u ∈ QAlgorithms.Papers.Independent.Support50.P12.spec D,
    ∑ v ∈ QAlgorithms.Papers.Independent.Support50.P12.spec D,
      (((v * f (u / v)) : ℝ) : ℂ) •
        (QAlgorithms.spectralProjector D u * B * QAlgorithms.spectralProjector D v)

end PetzFisher


