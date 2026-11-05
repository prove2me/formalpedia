-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_plusOp
-- name    : JRCurvedQFT_Symmetries_plusOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:16.928195+00:00
-- url     : https://prove2.me/theorems/7b0c4893-2868-4b94-8a6a-5682ea5ea134
-- title:
--   The operator $T^+=\Theta T^*\Theta$
-- statement:
--   For a densely defined operator $T$ on $\mathcal E$, the operator $T^+=\Theta T^*\Theta$ with domain $\Theta^{-1}D(T^*)$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, §3.2, p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory
open QAlgorithms.Papers.Independent.Intakethird100.P92

namespace JRCurvedQFT.Symmetries

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The operator `T⁺ = Θ T* Θ` of Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, §3.2, p. 4 ("the adjoint T⁺ = ΘT*Θ"), with domain
`D(T⁺) = Θ⁻¹ D(T*)`. -/
noncomputable def plusOp (r : ReflectionData E) (T : E →ₗ.[ℂ] E) : E →ₗ.[ℂ] E where
  domain := T.adjoint.domain.comap (r.theta.toLinearEquiv : E →ₗ[ℂ] E)
  toFun := (r.theta.toLinearEquiv : E →ₗ[ℂ] E) ∘ₗ T.adjoint.toFun ∘ₗ
    LinearMap.restrict (r.theta.toLinearEquiv : E →ₗ[ℂ] E) (fun _ hx => hx)

end JRCurvedQFT.Symmetries


