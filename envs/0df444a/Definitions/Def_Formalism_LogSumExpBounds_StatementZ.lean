-- Prove2me | Definitions.Def_Formalism_LogSumExpBounds_StatementZ
-- name    : Formalism_LogSumExpBounds_StatementZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:31.243355+00:00
-- url     : https://prove2.me/theorems/2b6988ba-d060-4d96-93c0-88010f337c94
-- title:
--   Statement Z
-- statement:
--   Definitions and structural lemmas for Statement Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/StatementZ.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.NuclearRankWeightBounds.Z
open Finset
def LatSum : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℕ) (La : AddSubgroup (Fin f → ℂ)) (x : Fin f → ℝ) (K : ℕ) (S : Finset (Fin f → ℂ)),
      (∀ o ∈ La, o ≠ 0 → 1 ≤ ∏ v, ‖o v‖) → (∀ v, 0 < x v) → ∏ v, x v < 1 → 3 ≤ K →
      (∀ o ∈ S, o ∈ La ∧ o ≠ 0) →
      ∑ o ∈ S, ∏ v, min 1 ((x v / ‖o v‖) ^ K)
        ≤ C ^ f * (∏ v, x v) ^ ((K : ℝ) - 5 / 2)
def ZLift : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℕ) (La : AddSubgroup (Fin f → ℂ)) (x : Fin f → ℝ) (K : ℕ)
      (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (Z : Finset (Fin f → ℂ)) (U : (Fin f → ℂ) → H) (B : ℝ),
      (∀ o ∈ La, o ≠ 0 → 1 ≤ ∏ v, ‖o v‖) → (∀ v, 0 < x v) → ∏ v, x v < 1 → 3 ≤ K →
      (∀ z ∈ Z, ∀ v, z v ≠ 0) →
      (∀ z ∈ Z, ∀ z' ∈ Z, (fun v => (z v)⁻¹ - (z' v)⁻¹) ∉ La → inner ℂ (U z) (U z') = 0) →
      (∀ A : Finset (Fin f),
        ∑ z ∈ Z, (∏ v ∈ A, (2 / (x v * ‖z v‖)) ^ (2 * K)) * ‖U z‖ ^ 2 ≤ B) →
      ∑ z ∈ Z, ∑ z' ∈ Z.erase z, ‖inner ℂ (U z) (U z')‖
        ≤ C ^ f * (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * B
end Formalism.NuclearRankWeightBounds.Z


