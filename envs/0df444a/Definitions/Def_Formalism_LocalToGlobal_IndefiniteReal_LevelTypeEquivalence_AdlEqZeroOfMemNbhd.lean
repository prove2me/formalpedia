-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_AdlEqZeroOfMemNbhd
-- name    : Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_AdlEqZeroOfMemNbhd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:36:20.397191+00:00
-- url     : https://prove2.me/theorems/f070f2df-9534-44a0-ab49-a585083113c2
-- title:
--   Adl Eq Zero Of Mem Nbhd
-- statement:
--   Definitions and structural lemmas for Adl Eq Zero Of Mem Nbhd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/AdlEqZeroOfMemNbhd.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
namespace Formalism.IndefR.Eqv.G5
variable {F : Type} [Field F] [NumberField F]
open scoped AdeleRing
variable (F) in

def adlNbhd : Set (AdeleRing (𝓞 F) F) :=
  {x | (∀ w, ‖x.1 w‖ < 1) ∧ ∀ v, x.2 v ∈ v.adicCompletionIntegers F}
end Formalism.IndefR.Eqv.G5


