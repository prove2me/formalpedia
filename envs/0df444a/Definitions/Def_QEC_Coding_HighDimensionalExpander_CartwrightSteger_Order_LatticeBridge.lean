-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T14:25:46.784906+00:00
-- url     : https://prove2.me/theorems/72d7239b-b03b-4d16-ae50-7afc49fa885c
-- title:
--   Lattice Bridge
-- statement:
--   Definitions and structural lemmas for Lattice Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/LatticeBridge.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def orderUnitToCyclicUnit
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →* (CyclicAlgebra P r)ˣ :=
  Units.map (cartwrightStegerOrderToCyclicAlgebra P r).toMonoidHom
noncomputable def orderUnitToGlobalGL
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  (Units.map (CyclicAlgebra P r).val.toRingHom).comp
    (orderUnitToCyclicUnit P r)
noncomputable def orderUnitToBuildingPGL
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  (cyclicUnitToBuildingPGL P r).comp (orderUnitToCyclicUnit P r)
noncomputable def cartwrightStegerOrderUnitGenerator
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    (CartwrightStegerOrder P r)ˣ :=
  cartwrightStegerOrderGenerator P r (constantClassRepresentative P r x)
noncomputable def CartwrightStegerOrderUnitLattice
    (P : BasePrime) (r : Rank) :
    Subgroup ((CartwrightStegerOrder P r)ˣ) :=
  Subgroup.closure (Set.range (cartwrightStegerOrderUnitGenerator P r))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


