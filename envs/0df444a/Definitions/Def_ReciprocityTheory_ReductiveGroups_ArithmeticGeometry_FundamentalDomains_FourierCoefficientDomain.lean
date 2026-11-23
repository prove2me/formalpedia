-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:51:36.897089+00:00
-- url     : https://prove2.me/theorems/d0074044-f241-42d5-a2b5-95cc3eb5e73d
-- title:
--   Fourier Coefficient Domain
-- statement:
--   Definitions and structural lemmas for Fourier Coefficient Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientDomain.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_Lemmata_GeneralBFactBisForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
section Cauchy
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
end Cauchy
section Param
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ}
end Param
section Dom
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E)
def ZbL (b : X.Ψ → Fin 2 → Fin 2 → ℂ) : Frame X.Ψ r →L[ℂ] Frame X.Ψ r :=
  LinearMap.toContinuousLinearMap
    { toFun := X.Zb u b
      map_add' x y := by
        funext τ
        show X.zmat u b τ * (mat x τ + mat y τ) = _
        rw [Matrix.mul_add]; rfl
      map_smul' c x := by
        funext τ
        show X.zmat u b τ * (c • mat x τ) = _
        rw [Matrix.mul_smul]; rfl }
end Dom
end
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain


