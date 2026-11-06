-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
-- name    : QEC_Bounds_BPTDisentangling_Sectors_Selection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:15:50.797194+00:00
-- url     : https://prove2.me/theorems/dbc95933-07c2-41d9-8eb2-6031b0fbcf6c
-- title:
--   Selection
-- statement:
--   Definitions and structural lemmas for Selection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def secondCutProjectorBbarM
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (Semantics.CompositeSystem (M.fourFactorB region)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  (tensorAssociatorUnitary (M.fourFactorB region) (M.fourFactorC region)
    (M.fourFactorD region)).conjOperator
      (TensorProduct.map (M.fourFactorProjectorBCLocal region)
        (1 : Semantics.Operator (M.fourFactorD region))) *
    TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
      (M.fourFactorProjectorCDLocal region)
noncomputable def secondCutCoordinateTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))
      (M.fourFactorSystem region) :=
  tensorAssociatorUnitary (M.fourFactorA region) (M.fourFactorB region)
    (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
noncomputable def secondCutCodeLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  overlapLiftLeft
      (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
      (M.fourFactorProjectorABLocal region) *
    overlapLiftRight (A := M.fourFactorA region)
      (M.secondCutProjectorBbarM region)
noncomputable def secondCutSectorLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  overlapLiftLeft
    (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
      (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component))
noncomputable def secondCutGlobalCoordinateTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  composeUnitaryTransport (M.fourFactorTransport region)
    (M.secondCutCoordinateTransport region).symm
noncomputable def secondCutPhysicalSectorProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    Semantics.Operator L.Register :=
  (M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
    ((M.fourFactorBCoordinateRelabel region).symm.conjOperator
      (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component))
noncomputable def secondCutDoubleInteractionCoefficient
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (cd cd' : Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (a a' : M.fourFactorA region) :
    Semantics.Operator (M.fourFactorB region) :=
  leftInteractionCoefficient
    (rightInteractionCoefficient (M.secondCutCodeLift region) cd cd') a a'
end BPTCommutingProjectorModel
end Bounds
end QEC


