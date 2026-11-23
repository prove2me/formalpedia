-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_HenselRoot
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_HenselRoot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:04:59.894541+00:00
-- url     : https://prove2.me/theorems/238bd8d6-8b82-470b-8441-e927685b30a1
-- title:
--   Hensel Root
-- statement:
--   Definitions and structural lemmas for Hensel Root, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/HenselRoot.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Filter Topology
namespace PI.LocalEndW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
end PI.LocalEndW


