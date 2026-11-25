-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LevelZeroUniformizerFrameUnipotentAndEmbedGL
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LevelZeroUniformizerFrameUnipotentAndEmbedGL
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:16:39.540909+00:00
-- url     : https://prove2.me/theorems/dc29c64d-bd73-46f3-93ba-2767518db5c5
-- title:
--   Level Zero Uniformizer Frame Unipotent And Embed GL
-- statement:
--   Definitions and structural lemmas for Level Zero Uniformizer Frame Unipotent And Embed GL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LevelZeroUniformizerFrameUnipotentAndEmbedGL.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
open scoped Classical
noncomputable section
namespace GlobalTheory.LevZeroUp
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LevZeroGen GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
def scal (ϖ : kˣ) : XIx (Fin κ) t 0 ⊕ Fin (s + 1) → k := Sum.elim 1 fun i => (ϖ : k) ^ (i.val + 1)
def back : XIx (Fin κ) t 0 ⊕ Fin (s + 1) → Fin κ ⊕ Fin (s + 1) :=
  fun r => (ixZero (Fin κ ⊕ Fin (s + 1)) t).symm ((stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)).symm r)
end GlobalTheory.LevZeroUp


