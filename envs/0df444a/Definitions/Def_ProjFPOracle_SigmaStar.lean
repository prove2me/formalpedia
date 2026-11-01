-- Prove2me | Definitions.Def_ProjFPOracle_SigmaStar
-- name    : ProjFPOracle_SigmaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:14.656054+00:00
-- url     : https://prove2.me/theorems/5da45adf-2ef0-4da4-b1f7-8f96f8276f16
-- title:
--   The noise covariance $\Sigma^*$
-- statement:
--   For a random vector $Z\in\mathbb R^d$ write $\operatorname{cov}(Z)=\mathbb E[(Z-\mathbb EZ)(Z-\mathbb EZ)^\top]$. The **noise covariance** of the problem is the sum of two covariance matrices,
--   $$
--   \Sigma^*:=\operatorname{cov}\big(\Phi_d(b_1-b)\big)+\operatorname{cov}\big(\Phi_d(L_1-L)\bar v\big).
--   $$
--   In projected coordinates, $\Phi_d(b_1-b)=h_1-\Phi_db$ and, since $\bar v\in\mathbb S$, $\Phi_d(L_1-L)\bar v=(A_1-M)\Phi_d\bar v$; so $\Sigma^*=\operatorname{cov}(h_1)+\operatorname{cov}\big((A_1-M)\Phi_d\bar v\big)$.
--
--   $\Sigma^*$ is the noise covariance at the target $\bar v$, and it determines the leading statistical term $\mathcal E_n(M,\Sigma^*)$.
--
--   **Formalization Note** Covariances are written entry by entry with Bochner integrals; they are applied only to square-integrable vectors.
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, §3.1.1, p.12

import Mathlib
import Definitions.Def_ProjFPOracle_Phi
import Definitions.Def_ProjFPOracle_projMat
import Definitions.Def_ProjFPOracle_vbar

open MeasureTheory Matrix

namespace ProjFPOracle

/-- **The covariance matrix of a random vector** `Z : Ω → ℝ^d`:
`cov(Z) := E[(Z − E Z)(Z − E Z)ᵀ]`, entry by entry. Used in the definition of `Σ^*` (Mou,
Pananjady & Wainwright, *Optimal Oracle Inequalities for Projected Fixed-Point Equations*,
arXiv:2012.05299v1, p.12).

**Formalization Note** Bochner integrals; the mission applies it only to square-integrable vectors
(`IsObsModel`), for which every integrand is integrable. -/
noncomputable def covMat {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun j k => ∫ ω, (Z ω j - ∫ ω', Z ω' j ∂P) * (Z ω k - ∫ ω', Z ω' k ∂P) ∂P

/-- **The noise covariance `Σ^*`** (arXiv:2012.05299v1, p.12):
`Σ^* := cov(Φ_d(b_1 − b)) + cov(Φ_d(L_1 − L) v̄)`, a sum of two covariance matrices.

**Formalization Note** In the projected coordinates of `IsObsModel`, `Φ_d(b_1 − b) = h_1 − Φ_d b`,
whose covariance is `cov(h_1)`, and, since `v̄ ∈ 𝕊`, `Φ_d(L_1 − L) v̄ = (A_1 − M) Φ_d v̄` with
`M = Φ_d L Φ_d^*`. -/
noncomputable def SigmaStar {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) (L : X →L[ℝ] X) (b : X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (h : ℕ → Ω → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  covMat P (h 1) + covMat P (fun ω => (A 1 ω - projMat L φ) *ᵥ Phi φ (vbar L b φ))

end ProjFPOracle


