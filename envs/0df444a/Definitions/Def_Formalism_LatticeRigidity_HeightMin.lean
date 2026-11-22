-- Prove2me | Definitions.Def_Formalism_LatticeRigidity_HeightMin
-- name    : Formalism_LatticeRigidity_HeightMin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:04:05.03134+00:00
-- url     : https://prove2.me/theorems/f9b52a85-c6b8-4da7-ada8-7bd9d3387548
-- title:
--   Height Min
-- statement:
--   Definitions and structural lemmas for Height Min, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMin.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SA.D2
def HeightMin : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (a : ι → ℝ) (κ : ℝ), 0 ≤ κ → (∀ v, 0 ≤ a v) →
    κ ^ (2 * Fintype.card ι) ≤ ∏ v, a v ^ 2 →
    (Fintype.card ι : ℝ) * κ ^ 2 ≤ ∑ v, a v ^ 2
end Formalism.SA.D2


