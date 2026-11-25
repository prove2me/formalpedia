-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFundT
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFundT
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:52:35.979216+00:00
-- url     : https://prove2.me/theorems/89dfbb98-de13-4326-9783-ac8b3dfcc24f
-- title:
--   Box Fund T
-- statement:
--   Definitions and structural lemmas for Box Fund T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/BoxFundT.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFund
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
namespace Formalism.L2.SG.NGCut.SplitEmbedding
section TriT
variable {P : Type} [Fintype P] [DecidableEq P] {α : P → Type} [∀ p, AddCommGroup (α p)]
  (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
  (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
  (τ : ∀ p, (∀ q, α q) → α p) (hτ : ∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
  (A : ∀ p, AddSubgroup (α p)) (F : ∀ p, Set (α p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)
end TriT
end Formalism.L2.SG.NGCut.SplitEmbedding


