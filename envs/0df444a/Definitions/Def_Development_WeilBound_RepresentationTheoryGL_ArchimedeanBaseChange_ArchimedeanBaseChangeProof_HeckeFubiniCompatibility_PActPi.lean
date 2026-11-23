-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:20.024207+00:00
-- url     : https://prove2.me/theorems/460d80d0-5680-4748-8507-f7d50c14a2e4
-- title:
--   PAct Pi
-- statement:
--   Definitions and structural lemmas for PAct Pi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace PositivityTheory.Rg.BcB.CG
section Split
variable {ι : Type} [DecidableEq ι] {X : Type}
def splitY (w : ι) (t : X) (z : {v // v ≠ w} → X) : ι → X := fun v => if h : v = w then t else z ⟨v, h⟩
variable {Idx : ι → Type}
def splitM [MeasurableSpace X] (w : ι) : (ι → X) ≃ᵐ X × ({v // v ≠ w} → X) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (· = w)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.piUnique fun _ : {v // v = w} => X) (MeasurableEquiv.refl _))
end Split
section Iter
variable {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
variable [One X]
end Iter
end PositivityTheory.Rg.BcB.CG
end


