-- Prove2me | Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_PrimesOverLiterature_RayPrimeCountQ
-- name    : Formalism_SharpRestriction_LevelLetterCocycles_PrimesOverLiterature_RayPrimeCountQ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:01.533505+00:00
-- url     : https://prove2.me/theorems/48a509b7-3757-469b-aad3-f1c34bac54f9
-- title:
--   Ray Prime Count Q
-- statement:
--   Definitions and structural lemmas for Ray Prime Count Q, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/PrimesOverLiterature/RayPrimeCountQ.lean

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_PrimesOverLiterature_RayPrimeCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.N.Lit.RayPrimeCountQ
open Formalism.MainNotions.N.Lit.RayLarger Formalism.MainNotions.N.Lit.RayPrimeCount
def Stmt : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ε' < 1 / 4 →
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
      ∀ (K : Fld) (d m : ℕ), Module.finrank ℚ K = 2 → 0 < d → 0 < m → 4 * d ∣ m →
        (∃ z ∈ K, z ^ 2 = -(d : Qb)) →
        ∀ Y : ℝ, 1 ≤ Y → C * Real.log (m : ℝ) ^ 2 ≤ Real.log Y →
          Y ^ (1 - ε') ≤ (count K m Y : ℝ)
example : 0 < (1 : ℕ) ∧ 0 < (4 : ℕ) ∧ 4 * 1 ∣ (4 : ℕ) := by decide
end Formalism.MainNotions.N.Lit.RayPrimeCountQ


