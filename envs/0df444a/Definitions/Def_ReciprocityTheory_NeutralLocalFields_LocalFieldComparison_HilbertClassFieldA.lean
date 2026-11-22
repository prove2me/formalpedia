-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
-- name    : ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:19:30.854809+00:00
-- url     : https://prove2.me/theorems/2b142c5e-a52e-41a6-8d6c-b856e16c2421
-- title:
--   Hilbert Class Field A
-- statement:
--   Definitions and structural lemmas for Hilbert Class Field A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HilbertClassFieldA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors
namespace ReciprocityTheory.Neutral.Bridge.HCF
section classGroup
variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']
theorem map_mem_nzd (g : R ≃+* R') (I : (Ideal R)⁰) : (I : Ideal R).map g ∈ (Ideal R')⁰ := by
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective g.injective, ← Ideal.zero_eq_bot]
  exact nonZeroDivisors.coe_ne_zero I
end classGroup
section inertia
variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
end inertia
end ReciprocityTheory.Neutral.Bridge.HCF


