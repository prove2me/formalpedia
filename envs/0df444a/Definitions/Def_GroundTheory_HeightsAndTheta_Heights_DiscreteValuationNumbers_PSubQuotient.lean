-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSubQuotient
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSubQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:50.475236+00:00
-- url     : https://prove2.me/theorems/37c1d109-5a59-44e8-8a1a-df21d3020f57
-- title:
--   PSub Quotient
-- statement:
--   Definitions and structural lemmas for PSub Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSubQuotient.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
section Rename
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end Rename
section Join
variable {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] {O : Type*} [CommRing O]
  [Algebra O Ω] {N r m : ℕ} {E U V : Type*} [AddCommGroup E] [Module Ω E] [AddCommGroup U]
  [Module Ω U] [AddCommGroup V] [Module Ω V]
variable [DecidableEq K]
end Join
end
end GroundTheory.Heights₂.Heights.NumbersDVR


