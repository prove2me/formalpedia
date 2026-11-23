-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Specmeas
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Specmeas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:49.757361+00:00
-- url     : https://prove2.me/theorems/f4b24c33-42b3-4eb3-b783-41f68043b318
-- title:
--   Specmeas
-- statement:
--   Definitions and structural lemmas for Specmeas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/Specmeas.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ComplexConjugate ComplexOrder CompactlySupported
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P.Specmeas
variable {X : Type} [TopologicalSpace X]
def ofR (g : C(X, ℝ)) : C(X, ℂ) := ⟨fun x => (g x : ℂ), by fun_prop⟩
@[simp] lemma ofR_apply (g : C(X, ℝ)) (x : X) : ofR g x = (g x : ℂ) := rfl
def reC (f : C(X, ℂ)) : C(X, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩
def imC (f : C(X, ℂ)) : C(X, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩
section
variable (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f))
include hΛ
end
variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
end PositivityTheory.Rg.BcB.E2.P.Specmeas
namespace PositivityTheory.Rg.BcB.E2.P
end PositivityTheory.Rg.BcB.E2.P
end


