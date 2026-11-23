-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
-- name    : Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:07.535826+00:00
-- url     : https://prove2.me/theorems/600c9a17-45a9-4c5b-8f5a-015b7b1b720f
-- title:
--   CBCard NC
-- statement:
--   Definitions and structural lemmas for CBCard NC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/UnitTraceSumBounds/CBCardNC.lean

import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBFiLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.MainNotions.Ext.CutB
def cBCardNC : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool), Fintype.card (cBNC ε) = cBp ε * cBq ε
def cBhsPP : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (z : cBNC ε → ℂ), cBhs (cBpp ε z) = 2 * ∑ pr : cBNC ε, ‖z pr‖ ^ 2
def cBHCGap : Prop :=
  ∀ (N : ℕ) (lam : Fin N → ℝ) (c : ℝ), StrictAnti lam → (∀ a, ∃ m : ℤ, lam a - c = m) →
    ∀ a b : Fin N, a < b → ((b.val : ℝ) - a.val) ≤ lam a - lam b
end Formalism.MainNotions.Ext.CutB


