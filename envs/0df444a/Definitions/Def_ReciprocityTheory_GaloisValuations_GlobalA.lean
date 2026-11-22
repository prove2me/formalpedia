-- Prove2me | Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
-- name    : ReciprocityTheory_GaloisValuations_GlobalA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:45:50.365457+00:00
-- url     : https://prove2.me/theorems/ab2d0941-9e4e-4547-8d26-3be024936227
-- title:
--   Global A
-- statement:
--   Definitions and structural lemmas for Global A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
namespace ReciprocityTheory.Gal
section krull
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]
end krull
section roots
variable {Ω : Type*} [Field Ω]
end roots
section exists_place
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
end exists_place
end ReciprocityTheory.Gal


