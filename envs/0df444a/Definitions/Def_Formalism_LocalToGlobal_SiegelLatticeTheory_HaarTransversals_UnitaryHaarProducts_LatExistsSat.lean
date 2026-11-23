-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsSat
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsSat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:38.573796+00:00
-- url     : https://prove2.me/theorems/8f1bf942-ada2-4863-bcbd-49dac4ebf4b8
-- title:
--   Lat Exists Sat
-- statement:
--   Definitions and structural lemmas for Lat Exists Sat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsSat.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
import Definitions.Def_Lemmata_MiscLemmasD_Imports
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
namespace Formalism.L2.SG.Pf.LatEx
section Sat
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
local notation "𝓕" => FractionalIdeal (nonZeroDivisors (𝓞 E)) E
def lineV (c : 𝓕) (v : V) : Submodule (𝓞 E) V :=
  Submodule.span (𝓞 E) {y | ∃ x : E, x ∈ c ∧ y = x • v}
end Sat
end Formalism.L2.SG.Pf.LatEx


