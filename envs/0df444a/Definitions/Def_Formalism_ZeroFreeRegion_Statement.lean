-- Prove2me | Definitions.Def_Formalism_ZeroFreeRegion_Statement
-- name    : Formalism_ZeroFreeRegion_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:14.857811+00:00
-- url     : https://prove2.me/theorems/8ffda8dd-9677-4f8b-aae1-7a884746f2ee
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/Statement.lean

import Definitions.Def_Formalism_StatementOC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
namespace Formalism.ZF
def ZeroFreeRegion : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0
def LogDerivRegion : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 2) ≤ s.re →
    ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C * Real.log (|s.im| + 2) ^ 2
def GzPNT : Prop :=
  ∃ c K : ℝ, 0 < c ∧ ∀ y : ℝ, 2 ≤ y →
    |Formalism.Gz y| ≤ K * y * Real.exp (-c * Real.sqrt (Real.log y))
end Formalism.ZF


