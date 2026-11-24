-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexIteratedLevelChainInFrame
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexIteratedLevelChainInFrame
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T22:00:27.507128+00:00
-- url     : https://prove2.me/theorems/697661a9-c125-4f69-a90c-42a9d1504f81
-- title:
--   First Vertex Iterated Level Chain In Frame
-- statement:
--   Definitions and structural lemmas for First Vertex Iterated Level Chain In Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FirstVertexIteratedLevelChainInFrame.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
namespace GlobalTheory.FirstVertexFrame
def epsEquiv (κ : ℕ) (t : Type) : Fin κ ≃ XIx (Fin κ) t 0 where
  toFun i := .inl (.inl i)
  invFun := Sum.elim (Sum.elim id fun i => i.elim0) fun p => p.1.elim0
  left_inv _ := rfl
  right_inv := by
    rintro ((i | i) | p)
    · rfl
    · exact i.elim0
    · exact p.1.elim0
section
variable {k : Type} [Field k] {t : Type} [Fintype t] [DecidableEq t] {κ l : ℕ}
def read (t : Type) [Fintype t] [DecidableEq t] (ϖ : kˣ) (H : 0 + l = l) :
    GL (XIx (Fin κ) t 0 ⊕ Fin l) k ≃* GL (Fin κ ⊕ Fin l) k :=
  (typeFrame ϖ (stdOrd (Fin κ) t 0 l H)).conj.symm.trans (reGL (ixZero (Fin κ ⊕ Fin l) t)).symm
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end
end GlobalTheory.FirstVertexFrame


