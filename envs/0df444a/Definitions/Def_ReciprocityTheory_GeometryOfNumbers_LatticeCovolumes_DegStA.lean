-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
-- name    : ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:54.481014+00:00
-- url     : https://prove2.me/theorems/d0464eec-bb20-46b3-8243-2ee45e287d35
-- title:
--   Deg St A
-- statement:
--   Definitions and structural lemmas for Deg St A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
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
section
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
end
section
variable {K : Type*} [Field K] [NumberField K]
end
end ReciprocityTheory.GeometryOfNumbersTheory


