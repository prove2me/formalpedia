-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_NnrealEqOneOfMulSelf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_NnrealEqOneOfMulSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:20.380698+00:00
-- url     : https://prove2.me/theorems/2e972409-b931-4dc5-a7ed-66eb0dc854be
-- title:
--   Nnreal Eq One Of Mul Self
-- statement:
--   Definitions and structural lemmas for Nnreal Eq One Of Mul Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/NnrealEqOneOfMulSelf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_MapPhiOfModM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Measure
open scoped NNReal
section Gen
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}
def trG (X : GL (Fin k) A) : GL (Fin k) A where
  val := (X : Matrix (Fin k) (Fin k) A).transpose
  inv := ((X⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).transpose
  val_inv := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]
end Gen
end PI.VolSemiDirect.W.Cj


