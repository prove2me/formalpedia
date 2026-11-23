-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsBasisOfLattice
-- name    : Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsBasisOfLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:12.147106+00:00
-- url     : https://prove2.me/theorems/25316ff9-df08-4b58-9ab6-13dda9c01636
-- title:
--   Exists Basis Of Lattice
-- statement:
--   Definitions and structural lemmas for Exists Basis Of Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/ExistsBasisOfLattice.lean

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.LOC
open Module
namespace Lat2
section SlopeTestRemainingChoices
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
section One
variable {V V' : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
  [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V'] [Module (FractionRing O) V']
  [IsScalarTower O (FractionRing O) V']
end One
end SlopeTestRemainingChoices
end Lat2
open Lat2
namespace Lat2
section Fib
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {VY VT VY' VT' : Type u}
  [AddCommGroup VY] [Module O VY] [Module (FractionRing O) VY] [IsScalarTower O (FractionRing O) VY]
  [AddCommGroup VT] [Module O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VY'] [Module O VY'] [AddCommGroup VT'] [Module O VT']
def pairB (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O) (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) :
    (VY × VT) →ₗ[O] (VT' × VY') →ₗ[O] FractionRing O :=
  bY.compl₁₂ (LinearMap.fst O VY VT) (LinearMap.snd O VT' VY') -
    bT.compl₁₂ (LinearMap.snd O VY VT) (LinearMap.fst O VT' VY')
end Fib
end Lat2
end Formalism.RepresentationBoundsCohomology.LOC


