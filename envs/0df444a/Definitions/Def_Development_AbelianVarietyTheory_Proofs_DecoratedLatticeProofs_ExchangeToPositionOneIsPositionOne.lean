-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeToPositionOneIsPositionOne
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeToPositionOneIsPositionOne
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:10:56.397089+00:00
-- url     : https://prove2.me/theorems/fa69c069-0249-4e27-9b41-735318b26729
-- title:
--   Exchange To Position One Is Position One
-- statement:
--   Definitions and structural lemmas for Exchange To Position One Is Position One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExchangeToPositionOneIsPositionOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Theorems.Thm_GlobalTheory_SplitWeil_om_isSmoothRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
noncomputable section
namespace GlobalTheory.PosOne.ToOnePos
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable {n' : Type} [Fintype n'] [DecidableEq n']
def omRep (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) : Representation ℂ (GL n k) (SB (Matrix n n' k)) where
  toFun g :=
    { toFun := fun Ψ => ⟨om μ 1 g Ψ.1,
        (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.2.1 1 g Ψ.1 Ψ.2⟩
      map_add' := fun Ψ Ψ' => by
        apply Subtype.ext
        have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.1 1 g 1 Ψ.1 Ψ'.1
        simpa using this
      map_smul' := fun z Ψ => by
        apply Subtype.ext
        have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.1 1 g z Ψ.1 0
        have h0 : om μ 1 g (0 : Matrix n n' k → ℂ) = 0 := by
          funext x
          simp [om]
        simpa [h0] using this }
  map_one' := by
    ext Ψ : 2
    exact (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).1 Ψ.1
  map_mul' g h := by
    ext Ψ : 2
    have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.1 1 1 g h Ψ.1
    simpa using this
end GlobalTheory.PosOne.ToOnePos


