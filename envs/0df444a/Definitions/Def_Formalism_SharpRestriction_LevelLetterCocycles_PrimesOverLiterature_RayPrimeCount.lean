-- Prove2me | Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_PrimesOverLiterature_RayPrimeCount
-- name    : Formalism_SharpRestriction_LevelLetterCocycles_PrimesOverLiterature_RayPrimeCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:49:47.203249+00:00
-- url     : https://prove2.me/theorems/f71ea12c-cc04-4df9-bab6-b4bbeb8d4577
-- title:
--   Ray Prime Count
-- statement:
--   Definitions and structural lemmas for Ray Prime Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/PrimesOverLiterature/RayPrimeCount.lean

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_PrimesOverLiterature_RayLarger
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.N.Lit.RayPrimeCount
open Formalism.MainNotions.N.Lit.RayLarger
noncomputable def count (K : Fld) (m : ℕ) (Y : ℝ) : ℕ :=
  Nat.card {p : ℕ // IsRayPrime K m p ∧ Y ≤ p ∧ (p : ℝ) ≤ 2 * Y}
def Stmt : Prop :=
  ∃ C'' C' : ℝ, ∀ (K : Fld) (d m : ℕ), Module.finrank ℚ K = 2 → 0 < d → 0 < m → 4 * d ∣ m →
    (∃ z ∈ K, z ^ 2 = -(d : Qb)) →
    ∀ X : ℝ, (m : ℝ) ^ (C'' + C') ≤ X →
      ∃ Y : ℝ, X * (m : ℝ) ^ (-C') ≤ Y ∧ Y ≤ X ∧ Y * (m : ℝ) ^ (-C'') / Real.log Y ≤ (count K m Y : ℝ)
end Formalism.MainNotions.N.Lit.RayPrimeCount


