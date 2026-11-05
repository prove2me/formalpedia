-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_spectralExpI
-- name    : JRCurvedQFT_Symmetries_spectralExpI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:17.369607+00:00
-- url     : https://prove2.me/theorems/d98ff9d3-9a80-4484-8f9f-a534cc78a637
-- title:
--   The operator $e^{i\alpha A}$ as a spectral integral
-- statement:
--   The operator $e^{i\alpha A}=\int_{\mathbb R}e^{i\alpha x}\,dP(x)$, where $P$ is the projection-valued measure of $A$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, Theorem 6.4, p. 11

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralIntegral

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory
open TeschlQM.Shared TeschlQM.Spectral

namespace JRCurvedQFT.Symmetries

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator `e^{iαA} = ∫ e^{iαx} dP(x)`, for `P` the projection-valued measure of `A`.
Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, Theorem 6.4, p. 11. -/
noncomputable def spectralExpI (P : Set ℝ → (H →L[ℂ] H)) (α : ℝ) : H →ₗ.[ℂ] H :=
  spectralIntegral P (fun x => Complex.exp (Complex.I * (α : ℂ) * (x : ℂ)))

end JRCurvedQFT.Symmetries


