-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_IsSpectralGenerator
-- name    : JRCurvedQFT_Symmetries_IsSpectralGenerator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:09.998587+00:00
-- url     : https://prove2.me/theorems/81f19fcb-e5b1-49cf-abf0-b260e65bd13f
-- title:
--   $P$ is the projection-valued measure of $A$
-- statement:
--   $P$ is a projection-valued measure on the Borel sets of $\mathbb R$ and $A=\int_{\mathbb R}x\,dP(x)$. Every self-adjoint operator has exactly one such $P$, and functions of $A$ are spectral integrals against it.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, Theorems 6.2 and 6.4, p. 11

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralIntegral

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory
open TeschlQM.Shared TeschlQM.Spectral

namespace JRCurvedQFT.Symmetries

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `P` is the **projection-valued measure of** the operator `A`: `A = ∫ x dP(x)`.

**Formalization Note** Reading 7: `e^{−αA}` and `e^{iαA}` of Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, Theorem 6.2 and Theorem 6.4,
p. 11, are the spectral integrals of `P`. -/
def IsSpectralGenerator (P : Set ℝ → (H →L[ℂ] H)) (A : H →ₗ.[ℂ] H) : Prop :=
  IsProjValuedMeasure P ∧ A = spectralIntegral P (fun x => (x : ℂ))

end JRCurvedQFT.Symmetries


