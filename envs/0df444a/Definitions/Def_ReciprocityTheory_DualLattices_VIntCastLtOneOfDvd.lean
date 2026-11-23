-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
-- name    : ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:29.784904+00:00
-- url     : https://prove2.me/theorems/3fa8ddee-ed03-48d6-89ef-d97c383e0fb5
-- title:
--   VInt Cast Lt One Of Dvd
-- statement:
--   Definitions and structural lemmas for VInt Cast Lt One Of Dvd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VIntCastLtOneOfDvd.lean

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
open Finset
namespace ReciprocityTheory.PGsh.Up.U3
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
end ReciprocityTheory.PGsh.Up.U3


