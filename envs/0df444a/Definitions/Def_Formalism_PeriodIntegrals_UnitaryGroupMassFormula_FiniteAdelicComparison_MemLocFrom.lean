-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:29.652585+00:00
-- url     : https://prove2.me/theorems/e53734dd-7c77-4d65-b2ac-266ae31ed59b
-- title:
--   Mem Loc From
-- statement:
--   Definitions and structural lemmas for Mem Loc From, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/MemLocFrom.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
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
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
def psiV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F →ₐ[I.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E :=
  (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v) (AlgHom.id I.F I.E)).comp
    (Algebra.TensorProduct.comm I.F I.E (Formalism.MainNotions.S.Af I.F)).toAlgHom
def vecV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    Fin I.n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E :=
  fun i => psiV I v (x i)
def MemLocTo : Prop :=
  ∀ (I : AutInst) (x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), x ∈ I.Lf →
    ∀ v, vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))
def MemLocFrom : Prop :=
  ∀ (I : AutInst) (x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F),
    (∀ v, vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) → x ∈ I.Lf
def InjV : Prop :=
  ∀ (I : AutInst) (z : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), (∀ v, psiV I v z = 0) → z = 0
def LiftV : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (y : Fin I.n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E),
    ∃ x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, vecV I v x = y ∧ ∀ w, w ≠ v → vecV I w x = 0
end PI.FinKW


