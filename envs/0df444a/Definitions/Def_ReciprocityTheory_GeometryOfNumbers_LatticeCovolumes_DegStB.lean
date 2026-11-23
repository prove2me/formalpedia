-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB
-- name    : ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:11:07.487808+00:00
-- url     : https://prove2.me/theorems/588a0ebf-f2a4-4768-8a75-4a803ffa692e
-- title:
--   Deg St B
-- statement:
--   Definitions and structural lemmas for Deg St B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStB.lean

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end ReciprocityTheory.GeometryOfNumbersTheory


