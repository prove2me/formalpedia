-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SigmaFiniteOfFcG
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SigmaFiniteOfFcG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:26:26.541129+00:00
-- url     : https://prove2.me/theorems/ed691f42-ac8b-4c08-832a-c89e2afa40f1
-- title:
--   Sigma Finite Of Fc G
-- statement:
--   Definitions and structural lemmas for Sigma Finite Of Fc G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SigmaFiniteOfFcG.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
def subOf (H : Set G) (h1 : (1 : G) ∈ H) (hm : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) (hi : ∀ x ∈ H, x⁻¹ ∈ H) :
    Subgroup G where
  carrier := H
  one_mem' := h1
  mul_mem' := fun {a b} ha hb => hm a ha b hb
  inv_mem' := fun {a} ha => hi a ha
end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore


