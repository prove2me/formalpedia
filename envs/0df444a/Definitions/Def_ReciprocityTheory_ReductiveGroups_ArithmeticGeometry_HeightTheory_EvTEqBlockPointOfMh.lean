-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_EvTEqBlockPointOfMh
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_EvTEqBlockPointOfMh
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:59.829013+00:00
-- url     : https://prove2.me/theorems/03d42be0-357c-4c4e-b806-f177fe367c1d
-- title:
--   Ev TEq Block Point Of Mh
-- statement:
--   Definitions and structural lemmas for Ev TEq Block Point Of Mh, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/EvTEqBlockPointOfMh.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
end Data
end ReciprocityTheory.ChartRestriction.G.T0


