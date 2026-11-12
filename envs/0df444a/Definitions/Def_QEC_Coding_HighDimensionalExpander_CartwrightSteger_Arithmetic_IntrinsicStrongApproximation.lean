-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T16:54:25.334002+00:00
-- url     : https://prove2.me/theorems/771fca84-3b9c-4ba9-8b94-5c357d59cc51
-- title:
--   Intrinsic Strong Approximation
-- statement:
--   Definitions and structural lemmas for Intrinsic Strong Approximation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
local instance intrinsicResidueFieldDiscreteTopologicalSpace
    (P : BasePrime) (r : Rank) (level : Nat) :
    TopologicalSpace (ResidueField P r level) := ⊥
local instance intrinsicResidueFieldDiscreteTopology
    (P : BasePrime) (r : Rank) (level : Nat) :
    DiscreteTopology (ResidueField P r level) := ⟨rfl⟩
noncomputable def baseNormOneOrderUnitsToCompleted
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerBaseNormOneOrderUnits P r →*
      IndexCompletedNormOneInnerForm P r level :=
  (orderNormOneInnerFormToCompleted P r level).comp
    (orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm.toMonoidHom
noncomputable def baseNormOneOrderUnitsReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerBaseNormOneOrderUnits P r →* PSL P r level :=
  (orderNormOneInnerFormReduction P r level).comp
    (orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm.toMonoidHom
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


