-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:16.474922+00:00
-- url     : https://prove2.me/theorems/62fedc2f-e079-4a63-ac09-0963cca71bc3
-- title:
--   Pair Base Of Lag
-- statement:
--   Definitions and structural lemmas for Pair Base Of Lag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/PairBaseOfLag.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LocCartanPair
open Matrix IsLocalRing
section Lag
variable {R : Type} [CommRing R] [StarRing R]
variable (κ : Type) [Fintype κ] [DecidableEq κ]
def hypJ : Matrix (κ ⊕ κ) (κ ⊕ κ) R := fromBlocks 0 1 1 0
def hypE : Matrix (κ ⊕ κ) (κ ⊕ κ) R := fromBlocks 1 0 0 0
end Lag
section Main
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
  [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
end Main
end PI.LocCartanPair


