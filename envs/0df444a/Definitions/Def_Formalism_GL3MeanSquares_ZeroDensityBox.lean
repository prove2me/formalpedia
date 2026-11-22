-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_ZeroDensityBox
-- name    : Formalism_GL3MeanSquares_ZeroDensityBox
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:35.129515+00:00
-- url     : https://prove2.me/theorems/045b7ee4-fd3c-482e-893e-3823e9afbe22
-- title:
--   Zero Density Box
-- statement:
--   Definitions and structural lemmas for Zero Density Box, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/ZeroDensityBox.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.ZeroDensityInBoxes
def ZeroDensityBox : Prop :=
  ∃ C : ℝ, ∀ (Q : ℝ) (S : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1))), 3 ≤ Q →
    (∀ p ∈ S, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0) →
    (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)
def BoxTailAll : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxTailHyp ε C x₀
def BoxCountOfZD : Prop :=
  ZeroDensityBox → ∃ C : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxCountHyp C
end Formalism.HermitianLattices.ZeroDensityInBoxes


