-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:29.42488+00:00
-- url     : https://prove2.me/theorems/4aeb14e4-036b-41c9-b729-0770a1cec438
-- title:
--   Lattice Point Count Scaling
-- statement:
--   Definitions and structural lemmas for Lattice Point Count Scaling, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticePointCountScaling.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
namespace GlobalTheory.CompanionTheory.RiemannCore
section
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]
def cell (D : Set G) (R : Finset G) : Set G := ⋃ r ∈ R, (fun y => -r + y) ⁻¹' D
def tile (D : Set G) (R : Finset G) (l : G) : Set G := (fun y => -l + y) ⁻¹' cell D R
end
end GlobalTheory.CompanionTheory.RiemannCore


