-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocLift
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocLift
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:30:56.161634+00:00
-- url     : https://prove2.me/theorems/13804bca-9801-4406-8a3f-a92c0415073a
-- title:
--   Loc Lift
-- statement:
--   Definitions and structural lemmas for Loc Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocLift.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.FinKW
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
open Classical in

def liftOne (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F :=
  (TensorProduct.equivFinsuppOfBasisRight (Module.Basis.ofVectorSpace I.F I.E) y).sum
    fun j c => Module.Basis.ofVectorSpace I.F I.E j ⊗ₜ[I.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV I.F v c
end PI.FinKW


