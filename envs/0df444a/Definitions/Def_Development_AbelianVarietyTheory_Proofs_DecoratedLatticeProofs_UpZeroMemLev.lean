-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:08:16.63033+00:00
-- url     : https://prove2.me/theorems/45cbb20b-7cfd-407f-9fb0-a2137f73170e
-- title:
--   Up Zero Mem Lev
-- statement:
--   Definitions and structural lemmas for Up Zero Mem Lev, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/UpZeroMemLev.lean

import Mathlib
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
namespace GlobalTheory.LevZeroGen
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
def xZero (κ t : Type) : κ ≃ XIx κ t 0 := (Equiv.sumEmpty κ (Fin 0)).symm.trans (Equiv.sumEmpty (κ ⊕ Fin 0) (Fin 0 × t)).symm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
def upZero : GL (Fin κ ⊕ Fin (s + 1)) k ≃* GL (XIx (Fin κ) t 0 ⊕ Fin (s + 1)) k :=
  (reGL (ixZero (Fin κ ⊕ Fin (s + 1)) t)).trans (typeFrame S.ϖ (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _))).conj
end GlobalTheory.LevZeroGen
end


