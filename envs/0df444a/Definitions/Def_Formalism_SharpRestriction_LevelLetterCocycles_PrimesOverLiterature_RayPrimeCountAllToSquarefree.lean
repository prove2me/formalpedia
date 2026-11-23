-- Prove2me | Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_PrimesOverLiterature_RayPrimeCountAllToSquarefree
-- name    : Formalism_SharpRestriction_LevelLetterCocycles_PrimesOverLiterature_RayPrimeCountAllToSquarefree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:52.828916+00:00
-- url     : https://prove2.me/theorems/19768d82-a874-46b6-a5a9-0ccfcbe277d9
-- title:
--   Ray Prime Count All To Squarefree
-- statement:
--   Definitions and structural lemmas for Ray Prime Count All To Squarefree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/PrimesOverLiterature/RayPrimeCountAllToSquarefree.lean

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_PrimesOverLiterature_RayPrimeCountQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.N.Lit.RayClassPrimeCountSquarefree
open Formalism.MainNotions.N.Lit.RayLarger Formalism.MainNotions.N.Lit.RayPrimeCount
def Stmt : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ε' < 1 / 4 →
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
      ∀ (K : Fld) (d m : ℕ), Module.finrank ℚ K = 2 → 0 < d → d.Prime → d % 4 = 3 → 0 < m → 4 * d ∣ m →
        (∃ z ∈ K, z ^ 2 = -(d : Qb)) →
        ∀ Y : ℝ, 1 ≤ Y → C * Real.log (m : ℝ) ^ 2 ≤ Real.log Y →
          Y ^ (1 - ε') ≤ (count K m Y : ℝ)
example : (3 : ℕ).Prime ∧ 3 % 4 = 3 ∧ 4 * 3 ∣ (12 : ℕ) := ⟨Nat.prime_three, rfl, dvd_refl _⟩
end Formalism.MainNotions.N.Lit.RayClassPrimeCountSquarefree


