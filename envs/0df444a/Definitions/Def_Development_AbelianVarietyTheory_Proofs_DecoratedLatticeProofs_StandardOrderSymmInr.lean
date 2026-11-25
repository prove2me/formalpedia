-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_StandardOrderSymmInr
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_StandardOrderSymmInr
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:07:53.92338+00:00
-- url     : https://prove2.me/theorems/0c3ccced-c64d-59f0-a2b5-132c9dd6d630
-- title:
--   Standard Order Symm Inr
-- statement:
--   Definitions and structural lemmas for Standard Order Symm Inr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/StandardOrderSymmInr.lean

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
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
namespace GlobalTheory.SymChain.NonZeroAt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
section Coords
variable {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}
end Coords
section Ord
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Ord
section Chain
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable (k) in

def Est (j : ℕ) : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (j + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) t j) k :=
  fun P Q => if P = ixSucc _ t j (.inl Q) then 1 else 0
def xst (j c : ℕ) (h : j + c = s) :
    Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k :=
  (typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega))).bas.val *
    (Est k (κ := κ) (s := s) t j).submatrix (stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)).symm
      (stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)).symm *
    ((typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega))).bas⁻¹).val
end Chain
section Entry
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
end Entry
section Main
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
end Main
section Final
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
end Final
end GlobalTheory.SymChain.NonZeroAt
namespace GlobalTheory.SymChain
end GlobalTheory.SymChain


