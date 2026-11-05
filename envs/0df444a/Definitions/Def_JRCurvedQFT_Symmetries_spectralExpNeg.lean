-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_spectralExpNeg
-- name    : JRCurvedQFT_Symmetries_spectralExpNeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:24.613371+00:00
-- url     : https://prove2.me/theorems/9d1cea81-94eb-415e-a937-f5b4a73629c3
-- title:
--   The operator $e^{-\alpha A}$ as a spectral integral
-- statement:
--   The operator $e^{-\alpha A}=\int_{\mathbb R}e^{-\alpha x}\,dP(x)$ with its natural domain $\{\psi:\int e^{-2\alpha x}\,d\mu_\psi(x)<\infty\}$, where $P$ is the projection-valued measure of $A$. It is unbounded when $A$ is not bounded below.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, Theorem 6.2, p. 11

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralIntegral

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory
open TeschlQM.Shared TeschlQM.Spectral

namespace JRCurvedQFT.Symmetries

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator `e^{−αA} = ∫ e^{−αx} dP(x)`, with its natural (possibly proper) domain, for `P` the
projection-valued measure of `A`. Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, Theorem 6.2, p. 11. -/
noncomputable def spectralExpNeg (P : Set ℝ → (H →L[ℂ] H)) (α : ℝ) : H →ₗ.[ℂ] H :=
  spectralIntegral P (fun x => ((Real.exp (-α * x) : ℝ) : ℂ))

end JRCurvedQFT.Symmetries


