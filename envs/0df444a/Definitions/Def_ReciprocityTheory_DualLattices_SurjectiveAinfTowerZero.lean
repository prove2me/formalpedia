-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_SurjectiveAinfTowerZero
-- name    : ReciprocityTheory_DualLattices_SurjectiveAinfTowerZero
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:34:41.482803+00:00
-- url     : https://prove2.me/theorems/52d976f5-09b7-5092-8300-9d4422805327
-- title:
--   Surjective Ainf Tower Zero
-- statement:
--   Definitions and structural lemmas for Surjective Ainf Tower Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SurjectiveAinfTowerZero.lean

import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
namespace ReciprocityTheory.PGsh.Be2
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
end ReciprocityTheory.PGsh.Be2


