-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_ExistsBox
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_ExistsBox
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:44.477349+00:00
-- url     : https://prove2.me/theorems/4fa28a54-c876-41ca-8b85-d099787ba1e9
-- title:
--   Exists Box
-- statement:
--   Definitions and structural lemmas for Exists Box, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/ExistsBox.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_PiMapMulRight
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
section Fac
variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
end Fac
section FacG
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, SecondCountableTopology (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, BorelSpace (G v)]
end FacG
end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM


