-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TypeFrameConjugationDecomposition
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TypeFrameConjugationDecomposition
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:47.729328+00:00
-- url     : https://prove2.me/theorems/511ff8ca-0129-5b41-af5a-784c6501044c
-- title:
--   Type Frame Conjugation Decomposition
-- statement:
--   Definitions and structural lemmas for Type Frame Conjugation Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.SymDec
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end
section Frame
variable {k : Type} [Field k] {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
def dg (ϖ : kˣ) : n ⊕ Fin c → k := Sum.elim (fun _ => 1) (fun i => (ϖ : k) ^ (i.val + 1))
end Frame
section Zero
variable {k : Type} [Field k] {κ c : ℕ} (t : Type) [Fintype t] [DecidableEq t]
def ordZ (hc : 0 + c = c) : Fin κ ⊕ Fin c ≃ XIx (Fin κ) t 0 ⊕ Fin c :=
  (ixZero (Fin κ ⊕ Fin c) t).trans (stdOrd (Fin κ) t 0 c hc)
def epsZ : Fin κ ≃ XIx (Fin κ) t 0 :=
  (Equiv.sumEmpty (Fin κ) (Fin 0)).symm.trans (Equiv.sumEmpty (Fin κ ⊕ Fin 0) (Fin 0 × t)).symm
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Zero
end GlobalTheory.SymDec
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain


