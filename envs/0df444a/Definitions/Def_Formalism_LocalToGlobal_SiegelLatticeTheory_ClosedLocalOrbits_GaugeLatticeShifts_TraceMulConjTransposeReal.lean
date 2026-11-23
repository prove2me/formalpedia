-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_TraceMulConjTransposeReal
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_TraceMulConjTransposeReal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:33:38.972796+00:00
-- url     : https://prove2.me/theorems/9cb1c15b-fcc2-449f-ab36-664935988afa
-- title:
--   Trace Mul Conj Transpose Real
-- statement:
--   Definitions and structural lemmas for Trace Mul Conj Transpose Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/TraceMulConjTransposeReal.lean

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace Formalism.MainNotions.S.Gauge.Cd
variable {P Q : ℕ}
local notation "ι" => Fin P ⊕ Fin Q
def hs2 (Z : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (Z i j)
end Formalism.MainNotions.S.Gauge.Cd


