-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPow
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPow
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:56:11.033377+00:00
-- url     : https://prove2.me/theorems/d2364bd2-55b4-4b61-b544-419aa7c34dbd
-- title:
--   Inert Pow
-- statement:
--   Definitions and structural lemmas for Inert Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertPow.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
abbrev Av (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Type :=
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E
instance charZero_Fv (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    CharZero (v.adicCompletion I.F) :=
  charZero_of_injective_algebraMap (algebraMap I.F (v.adicCompletion I.F)).injective
def InR (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α z : Av I v) : Prop :=
  ∃ a b : v.adicCompletion I.F, a ∈ v.adicCompletionIntegers I.F ∧ b ∈ v.adicCompletionIntegers I.F ∧
    z = incL I v a + incL I v b * α
end PI.UnitaryGroupMassFormula.AdIndexEq
end


