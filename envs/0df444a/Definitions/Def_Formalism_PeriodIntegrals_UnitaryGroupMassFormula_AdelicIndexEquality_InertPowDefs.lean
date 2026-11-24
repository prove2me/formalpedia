-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:31:41.321632+00:00
-- url     : https://prove2.me/theorems/32983fa6-530c-4a3c-8f1b-84977a7ffff0
-- title:
--   Inert Pow Defs
-- statement:
--   Definitions and structural lemmas for Inert Pow Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertPowDefs.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
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
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
def incL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E :=
  Algebra.TensorProduct.includeLeftRingHom
def TraceInt : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E, sigV I v α * α = 1 →
      ∃ t ∈ v.adicCompletionIntegers I.F, α + sigV I v α = incL I v t
end PI.UnitaryGroupMassFormula.AdIndexEq
end


