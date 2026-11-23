-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:28.762075+00:00
-- url     : https://prove2.me/theorems/45829e7c-80e8-4a26-9dce-de867ab1e8dc
-- title:
--   Fixed Point Imaginary Span
-- statement:
--   Definitions and structural lemmas for Fixed Point Imaginary Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FixedPointImaginarySpan.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
  ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)
end
end ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan


