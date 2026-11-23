-- Prove2me | Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
-- name    : ReciprocityTheory_Automorphisms_InstMainA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:54:04.929575+00:00
-- url     : https://prove2.me/theorems/5d0451d1-f862-4d25-a595-1a4410a3b9c6
-- title:
--   Inst Main A
-- statement:
--   Definitions and structural lemmas for Inst Main A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/InstMainA.lean

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
namespace ReciprocityTheory.Aut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
end ReciprocityTheory.Aut


