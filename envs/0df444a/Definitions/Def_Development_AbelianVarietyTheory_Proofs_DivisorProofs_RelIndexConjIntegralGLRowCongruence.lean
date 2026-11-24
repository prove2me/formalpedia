-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:26.609546+00:00
-- url     : https://prove2.me/theorems/ec009bcf-e73f-4ade-8a06-0e4af302f2b4
-- title:
--   Rel Index Conj Integral GLRow Congruence
-- statement:
--   Definitions and structural lemmas for Rel Index Conj Integral GLRow Congruence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.DiagVol.RowIdx
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem mapInt_injective :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := ι) (algebraMap 𝒪[k] k)) := by
  intro u v h
  ext i j
  exact congrArg (fun g : GL ι k => g.val i j) h
def red : KO k ι →* GL ι 𝓀[k] :=
  (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k])).comp
    (MonoidHom.ofInjective (mapInt_injective (k := k) (ι := ι))).symm.toMonoidHom
end GlobalTheory.DiagVol.RowIdx


