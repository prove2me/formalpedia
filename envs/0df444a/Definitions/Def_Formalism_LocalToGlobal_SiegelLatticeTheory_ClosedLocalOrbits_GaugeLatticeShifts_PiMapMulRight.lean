-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_PiMapMulRight
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_PiMapMulRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:33.250163+00:00
-- url     : https://prove2.me/theorems/ff16aec5-2915-40f3-9a0a-6528c50ee300
-- title:
--   Pi Map Mul Right
-- statement:
--   Definitions and structural lemmas for Pi Map Mul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/PiMapMulRight.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LintegralFinProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal
namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
section Dens
variable {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
end Dens
section Grp
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)]
  [∀ i, MeasurableMul (G i)]
end Grp
section Uniq
end Uniq
end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM


