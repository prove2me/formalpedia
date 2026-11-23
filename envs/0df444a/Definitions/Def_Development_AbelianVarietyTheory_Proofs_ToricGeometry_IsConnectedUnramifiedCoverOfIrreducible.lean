-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedUnramifiedCoverOfIrreducible
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedUnramifiedCoverOfIrreducible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:39.339376+00:00
-- url     : https://prove2.me/theorems/aeaa6a13-cf1a-4e0b-baa9-ca2671937b60
-- title:
--   Is Connected Unramified Cover Of Irreducible
-- statement:
--   Definitions and structural lemmas for Is Connected Unramified Cover Of Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedUnramifiedCoverOfIrreducible.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory.SimpleRoots
open Polynomial
variable {d : ℕ}
open Classical in

noncomputable def partialProd (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (u : Set ((Fin d → ℂ) × ℂ)) (x : Fin d → ℂ) : ℂ[X] :=
  (((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u).map fun y => X - C y).prod
end GlobalTheory.SimpleRoots
namespace GlobalTheory
open SimpleRoots
end GlobalTheory


