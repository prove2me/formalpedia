-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelAllNonFreeUnreadEntries
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelAllNonFreeUnreadEntries
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:06:34.593372+00:00
-- url     : https://prove2.me/theorems/6ee22f9f-3037-4a45-aa22-b8277f15f9a2
-- title:
--   Flat Factor Reduction Kernel All Non Free Unread Entries
-- statement:
--   Definitions and structural lemmas for Flat Factor Reduction Kernel All Non Free Unread Entries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFactorReductionKernelAllNonFreeUnreadEntries.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
namespace GlobalTheory.FlatFactor.LowStage
section Shear
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
end Shear
section Transv
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] {c : ℕ}
def tv (i j : Fin c) (h : i ≠ j) (a : k) : GL (Fin c) k :=
  ⟨transvection i j a, transvection i j (-a),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩
end Transv
section PiLocalization₂
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)
open Classical in

def evStage (i : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  (evAll n n' c ρ).filter fun e => ∀ q, e.2 = Sum.inr q → q.val ≤ i
variable {n n' c ρ}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
end PiLocalization₂
end GlobalTheory.FlatFactor.LowStage


