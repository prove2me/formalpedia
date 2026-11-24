-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_G2EqZeroOfHasCMByThree
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_G2EqZeroOfHasCMByThree
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:44:12.752174+00:00
-- url     : https://prove2.me/theorems/6f3df821-e733-4eed-8ebf-df10d461bf40
-- title:
--   G2 Eq Zero Of Has CMBy Three
-- statement:
--   Definitions and structural lemmas for G2 Eq Zero Of Has CMBy Three, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/G2EqZeroOfHasCMByThree.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
namespace ReciprocityTheory.ChartRestriction.L1
theorem omegaK_three_sq : omegaK 3 ^ 2 = omegaK 3 - 1 := by
  have h : (((Real.sqrt (3 : ℕ) : ℝ) : ℂ)) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  unfold omegaK
  linear_combination (Complex.I ^ 2 / 4) * h + (3 / 4 : ℂ) * Complex.I_sq
def mulOmegaEquiv (L : PeriodPair) (hCM : HasCMBy 3 L) : L.lattice ≃ L.lattice where
  toFun l := ⟨omegaK 3 * l, hCM l l.2⟩
  invFun l := ⟨(l : ℂ) - omegaK 3 * l, L.lattice.sub_mem l.2 (hCM l l.2)⟩
  left_inv l := by
    apply Subtype.ext
    show omegaK 3 * (l : ℂ) - omegaK 3 * (omegaK 3 * l) = l
    linear_combination (-(l : ℂ)) * omegaK_three_sq
  right_inv l := by
    apply Subtype.ext
    show omegaK 3 * ((l : ℂ) - omegaK 3 * l) = l
    linear_combination (-(l : ℂ)) * omegaK_three_sq
end ReciprocityTheory.ChartRestriction.L1


