-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeIntegral
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:32.913661+00:00
-- url     : https://prove2.me/theorems/33cae4f0-30ec-4e2d-b778-d11266d32e9a
-- title:
--   Fourier Cube Integral
-- statement:
--   Definitions and structural lemmas for Fourier Cube Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCubeIntegral.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
  MeasureTheory Set Filter
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {u : Fin 2 → Fin r → E} {g : ℕ} {ω : Fin (4 * Fintype.card X.Ψ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
  {G : Frame X.Ψ r → ℂ}
end
end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral


