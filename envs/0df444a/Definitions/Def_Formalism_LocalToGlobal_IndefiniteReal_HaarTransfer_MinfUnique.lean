-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_MinfUnique
-- name    : Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_MinfUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:16.951526+00:00
-- url     : https://prove2.me/theorems/53315725-1777-4a42-9d77-56e33ba6063e
-- title:
--   Minf Unique
-- statement:
--   Definitions and structural lemmas for Minf Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HaarTransfer/MinfUnique.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.IndefR.Leaf
open MeasureTheory Formalism.BasicNotions
def MinfExistsUnique : Prop :=
  ∀ (p q : ℕ) (c : ENNReal), c ≠ 0 → c ≠ ⊤ →
    ∃! m : Measure (UpqT p q), m.IsHaarMeasure ∧ OmegaDensity m c
end Formalism.IndefR.Leaf


