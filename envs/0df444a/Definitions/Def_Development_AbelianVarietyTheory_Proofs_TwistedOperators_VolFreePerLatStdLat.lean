-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VolFreePerLatStdLat
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_VolFreePerLatStdLat
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:45.099914+00:00
-- url     : https://prove2.me/theorems/ff68cf89-fc40-4ad1-ae38-f2d0e5fe6709
-- title:
--   Vol Free Per Lat Std Lat
-- statement:
--   Definitions and structural lemmas for Vol Free Per Lat Std Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/VolFreePerLatStdLat.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
namespace GlobalTheory.RootEx.UnfoldShape
def boxExp {n n' : Type} {c : ℕ} : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → ℕ
  | (_, Sum.inl _) => 0
  | (Sum.inl _, Sum.inr j) => j.val
  | (Sum.inr l, Sum.inr j) => j.val - (l.val + 1)
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end
end GlobalTheory.RootEx.UnfoldShape


