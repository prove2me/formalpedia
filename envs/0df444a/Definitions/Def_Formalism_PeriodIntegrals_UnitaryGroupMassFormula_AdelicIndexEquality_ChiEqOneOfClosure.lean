-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:31:21.400908+00:00
-- url     : https://prove2.me/theorems/818be0c3-1699-49a4-887f-f235fc726385
-- title:
--   Chi Eq One Of Closure
-- statement:
--   Definitions and structural lemmas for Chi Eq One Of Closure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/ChiEqOneOfClosure.lean

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
def IsQRefl (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (s : Uv I v) : Prop :=
  ∃ (P : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E))
    (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E),
    P * P = P ∧ sigV I v α * α = 1 ∧
      (((s : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) = 1 + (α - 1) • P)
def QReflGen : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ g : Uv I v, g ∈ Subgroup.closure {s : Uv I v | IsQRefl I v s}
def QReflPow : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ s : Uv I v, IsQRefl I v s →
      ∃ m : ℕ, 1 ≤ m ∧ (((s ^ m : Uv I v) : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) ∈ Kv I v)
end PI.UnitaryGroupMassFormula.AdIndexEq
end


