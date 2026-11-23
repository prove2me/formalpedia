-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
-- name    : GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:06.053729+00:00
-- url     : https://prove2.me/theorems/580b0cb7-a5a5-4341-851e-8195d515e21d
-- title:
--   Frobenius
-- statement:
--   Definitions and structural lemmas for Frobenius, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace GroundTheory.Global
namespace Cyclotomic
section Frobenius
variable {m : ℕ} [NeZero m] (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]
variable (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
end Frobenius
end Cyclotomic
end GroundTheory.Global


