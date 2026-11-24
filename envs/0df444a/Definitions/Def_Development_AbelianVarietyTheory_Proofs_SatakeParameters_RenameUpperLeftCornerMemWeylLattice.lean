-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_RenameUpperLeftCornerMemWeylLattice
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_RenameUpperLeftCornerMemWeylLattice
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:21:39.832806+00:00
-- url     : https://prove2.me/theorems/ede8a48e-42dd-401f-8075-2829c819d055
-- title:
--   Rename Upper Left Corner Mem Weyl Lattice
-- statement:
--   Definitions and structural lemmas for Rename Upper Left Corner Mem Weyl Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/RenameUpperLeftCornerMemWeylLattice.lean

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
namespace GlobalTheory
namespace WeylRankEmbed
variable (R : Type) [CommRing R] {a b : ℕ} (hab : a ≤ b)
abbrev corner : Fin a × Fin a → Fin b × Fin b :=
  fun v => (Fin.castLE hab v.1, Fin.castLE hab v.2)
end WeylRankEmbed
end GlobalTheory


