-- Prove2me | Definitions.Def_Formalism_CoboundaryTransfers_StatementEx
-- name    : Formalism_CoboundaryTransfers_StatementEx
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:50.507926+00:00
-- url     : https://prove2.me/theorems/c7ede982-75c5-4c98-888b-c9918c9fab21
-- title:
--   Statement Ex
-- statement:
--   Definitions and structural lemmas for Statement Ex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/StatementEx.lean

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CoboundaryTransfers
def NonemptyG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ (B : Base ℤ_[p] (Polynomial ℤ_[p]))
    (W : WachMod B 0 (FractionRing (Polynomial ℤ_[p]))),
    B.p = p ∧ W.N ≠ ⊥ ∧ ¬ IsUnit B.X ∧ ¬ IsUnit B.Q ∧ B.φ B.X = B.X * B.Q ∧
    B.GammaX (-1) ∧ B.GammaQ ∧ (∃ x, W.γ x ≠ x)
end Formalism.CoboundaryTransfers


