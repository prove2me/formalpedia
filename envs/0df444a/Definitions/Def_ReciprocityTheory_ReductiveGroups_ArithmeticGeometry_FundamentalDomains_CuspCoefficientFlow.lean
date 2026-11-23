-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:44.977991+00:00
-- url     : https://prove2.me/theorems/a0cb9de9-8615-48bb-b88a-33c73b8e0e7e
-- title:
--   Cusp Coefficient Flow
-- statement:
--   Definitions and structural lemmas for Cusp Coefficient Flow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CuspCoefficientFlow.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
section Param
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type} [Fintype ι]
end Param
section Frame
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def flowL (ξ : Fin r → E) (s : X.Ψ → ℝ) : Frame X.Ψ r →L[ℂ] Frame X.Ψ r :=
  LinearMap.toContinuousLinearMap
    { toFun := X.flow ξ (fun τ => (s τ : ℂ))
      map_add' x y := by
        funext τ
        show X.flowMat ξ τ (s τ : ℂ) * (mat x τ + mat y τ) = _
        rw [Matrix.mul_add]; rfl
      map_smul' c x := by
        funext τ
        show X.flowMat ξ τ (s τ : ℂ) * (c • mat x τ) = _
        rw [Matrix.mul_smul]; rfl }
end Frame
end
end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow


