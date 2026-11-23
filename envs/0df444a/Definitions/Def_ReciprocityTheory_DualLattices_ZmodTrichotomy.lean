-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ZmodTrichotomy
-- name    : ReciprocityTheory_DualLattices_ZmodTrichotomy
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:09.452958+00:00
-- url     : https://prove2.me/theorems/b52c66d0-f022-4bca-9e86-b0e860321f13
-- title:
--   Zmod Trichotomy
-- statement:
--   Definitions and structural lemmas for Zmod Trichotomy, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ZmodTrichotomy.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_MulIterateRootEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal TensorProduct
namespace ReciprocityTheory.PGsh
section Principal
variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
end Principal
section ZModSq
variable (p : ℕ) [hp : Fact p.Prime]
end ZModSq
section Main
variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
end Main
end ReciprocityTheory.PGsh


