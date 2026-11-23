-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteSupportAdmissible
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteSupportAdmissible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:24.609905+00:00
-- url     : https://prove2.me/theorems/0b28504d-bca9-485b-924e-5294d4b2f0af
-- title:
--   Finite Support Admissible
-- statement:
--   Definitions and structural lemmas for Finite Support Admissible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteSupportAdmissible.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
namespace GlobalTheory
namespace AdmissibleFiniteSupport
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
end AdmissibleFiniteSupport
end GlobalTheory


