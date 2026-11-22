-- Prove2me | Definitions.Def_Formalism_SobolevGaussianKernels_StatementSB
-- name    : Formalism_SobolevGaussianKernels_StatementSB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:42:09.615077+00:00
-- url     : https://prove2.me/theorems/494ee994-e856-4df9-83c1-00fa52f53963
-- title:
--   Statement SB
-- statement:
--   Definitions and structural lemmas for Statement SB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/StatementSB.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SL.SB
open MeasureTheory
open scoped ContDiff
noncomputable def pd {n : ℕ} (i : Fin n) (g : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  fun y => fderiv ℝ g y (Pi.single i 1)
noncomputable def mixed {n : ℕ} (α : Finset (Fin n)) (g : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  (α.sort (· ≤ ·)).foldr pd g
def cube {n : ℕ} (a : Fin n → ℝ) (δ : ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (a i) (a i + δ))
def SobolevN : Prop :=
  ∀ (n : ℕ) (φ : (Fin n → ℝ) → ℂ) (a : Fin n → ℝ) (δ : ℝ),
    ContDiff ℝ ∞ φ → 0 < δ →
    ∀ x ∈ cube a δ,
      ‖φ x‖ ^ 2 ≤ 2 ^ n / δ ^ n *
        ∫ y in cube a δ, (∑ α : Finset (Fin n), δ ^ (2 * α.card) * ‖mixed α φ y‖ ^ 2)
end Formalism.SL.SB


