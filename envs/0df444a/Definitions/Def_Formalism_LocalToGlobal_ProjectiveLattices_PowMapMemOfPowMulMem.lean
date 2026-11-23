-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:46.626283+00:00
-- url     : https://prove2.me/theorems/66f4b668-3dc8-4691-8d54-df68d2f60651
-- title:
--   Pow Map Mem Of Pow Mul Mem
-- statement:
--   Definitions and structural lemmas for Pow Map Mem Of Pow Mul Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PowMapMemOfPowMulMem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.GenericSectionMinimum
structure IsDer {A : Type*} [CommRing A] (δ : A → A) : Prop where
  add : ∀ x y, δ (x + y) = δ x + δ y
  mul : ∀ x y, δ (x * y) = x * δ y + y * δ x
namespace IsDer
variable {A : Type*} [CommRing A] {δ : A → A}
end IsDer
end Formalism.L2.Pj.GenericSectionMinimum


