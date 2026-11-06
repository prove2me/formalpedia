-- Prove2me | Definitions.Def_QEC_Semantics_Entropy_QuditBounds
-- name    : QEC_Semantics_Entropy_QuditBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:09:17.211197+00:00
-- url     : https://prove2.me/theorems/fcb2ed2c-5663-4157-b749-8dc5f3f3c12f
-- title:
--   Qudit Bounds
-- statement:
--   Definitions and structural lemmas for Qudit Bounds, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder
noncomputable section
namespace DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
end DensityOperator
namespace Qudit
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
end Qudit
namespace QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι -> Nat}
end QuditSubsystem
end
end Semantics
end QEC


