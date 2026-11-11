-- Prove2me | Definitions.Def_ProdMixedTomo_TraceDistance
-- name    : ProdMixedTomo_TraceDistance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:04.265713+00:00
-- url     : https://prove2.me/theorems/9aa6e0a8-9ba4-46d0-ab36-aa9bc3497fde
-- title:
--   Trace distance $d_{\mathrm{tr}}$ and $\mathrm{opt}=\inf_{\pi\in\mathcal M_n}d_{\mathrm{tr}}(\pi,\rho)$
-- statement:
--   For Hermitian $A$ with eigenvalues $\lambda_1,\dots,\lambda_d$ the trace norm is $\|A\|_1=\sum_i|\lambda_i|$. The **trace distance** of two density matrices is
--   $$
--   d_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1 ,
--   $$
--   and the agnostic benchmark of an $n$-qubit state $\rho$ is its distance to the nearest product mixed state,
--   $$
--   \mathrm{opt}(\rho)=\inf_{\pi\in\mathcal M_n} d_{\mathrm{tr}}(\pi,\rho).
--   $$
--
--   Every guarantee of the tomography half of the mission is measured in $d_{\mathrm{tr}}$ relative to $\mathrm{opt}$.
--
--   **Formalization Note** The trace norm is computed from the eigenvalues of the Hermitian matrix (`Matrix.IsHermitian.eigenvalues`); it is only applied to differences of density matrices, which are Hermitian. $\mathrm{opt}$ is the infimum of a nonempty set bounded below by $0$.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §2 Notation and Problem 1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_ProdMixedTomo_States

namespace ProdMixedTomo

/-!
# Trace norm, trace distance and the agnostic benchmark `opt`

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §2 Notation and Problem 1, p.13
(PDF p.15): `d_tr(ρ, σ) = ½‖ρ − σ‖₁`, `opt = inf_{π ∈ M_n} d_tr(π, ρ)`.

**Formalization Note.** The trace norm of a Hermitian matrix is the sum of the absolute values of
its eigenvalues (`Matrix.IsHermitian.eigenvalues`); it is only ever applied to differences of
density matrices, which are Hermitian (the value `0` on non-Hermitian input is never used).
`opt` is the infimum of a nonempty set of reals bounded below by `0`.
-/

/-- The trace norm `‖A‖₁ = Σ |λᵢ(A)|` of a Hermitian matrix (`0` if `A` is not Hermitian). -/
noncomputable def traceNormH {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℂ) : ℝ :=
  if h : A.IsHermitian then ∑ i, |h.eigenvalues i| else 0

/-- The trace distance `d_tr(ρ, σ) = ½‖ρ − σ‖₁`. -/
noncomputable def dtr {κ : Type*} [Fintype κ] [DecidableEq κ] (ρ σ : Matrix κ κ ℂ) : ℝ :=
  traceNormH (ρ - σ) / 2

/-- `opt(ρ) = inf_{π ∈ M_n} d_tr(π, ρ)`, the distance to the nearest product mixed state. -/
noncomputable def optM {n : ℕ} (ρ : QMat n) : ℝ :=
  sInf ((fun σ => dtr σ ρ) '' ProductMixed n)

end ProdMixedTomo


