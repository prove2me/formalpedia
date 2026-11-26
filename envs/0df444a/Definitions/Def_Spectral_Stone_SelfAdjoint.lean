-- Prove2me | Definitions.Def_Spectral_Stone_SelfAdjoint
-- name    : Spectral_Stone_SelfAdjoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:54:13.508709+00:00
-- url     : https://prove2.me/theorems/da04ef15-a59b-425b-b8f1-dc33d76a992d
-- title:
--   Self Adjoint
-- statement:
--   Definitions and structural lemmas for Self Adjoint, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/SelfAdjoint.lean

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_Spectral_Stone_Generator
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace StrongContUnitary
open MeasureTheory Filter
def timeReverse (U : StrongContUnitary E) :
    StrongContUnitary E where
  toFun t := U.toFun (-t)
  isUnitary t := U.isUnitary (-t)
  zero := by
    simpa only [neg_zero] using U.zero
  add s t := by
    calc
      U.toFun (-(s + t)) = U.toFun ((-s) + (-t)) := by congr 1; ring
      _ = U.toFun (-s) * U.toFun (-t) := U.add (-s) (-t)
  stronglyContinuous x := (U.stronglyContinuous x).comp continuous_neg
end StrongContUnitary


