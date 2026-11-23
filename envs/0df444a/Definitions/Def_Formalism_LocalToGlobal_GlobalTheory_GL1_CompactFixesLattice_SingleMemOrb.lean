-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_SingleMemOrb
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_SingleMemOrb
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:45.266271+00:00
-- url     : https://prove2.me/theorems/8a5d797d-54d4-4d6f-a4e0-f1c74070fb35
-- title:
--   Single Mem Orb
-- statement:
--   Definitions and structural lemmas for Single Mem Orb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/SingleMemOrb.lean

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def orb {k : ℕ} (U : Subgroup (GL (Fin k) (AE F E))) : Submodule (SS F E) (Fin k → AE F E) :=
  Submodule.span (SS F E) {y | ∃ g ∈ U, ∃ j : Fin k,
    y = (g : Matrix (Fin k) (Fin k) (AE F E)) *ᵥ (Pi.single j 1 : Fin k → AE F E)}
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
end


