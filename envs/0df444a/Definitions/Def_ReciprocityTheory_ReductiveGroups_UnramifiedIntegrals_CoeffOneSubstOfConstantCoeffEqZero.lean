-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:25.017824+00:00
-- url     : https://prove2.me/theorems/8308f5da-b34b-4540-8f49-16275a1a0ccd
-- title:
--   Coeff One Subst Of Constant Coeff Eq Zero
-- statement:
--   Definitions and structural lemmas for Coeff One Subst Of Constant Coeff Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
section Field
variable {K : Type} [Field K] (g2 g3 : K)
theorem uSer_coeff_one : coeff 1 (uSer g2 g3) = 1 := by
  unfold uSer
  rw [mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
    map_mul, constantCoeff_inv]
  unfold wpNum wpDen
  simp [← coeff_zero_eq_constantCoeff_apply]
theorem isUnit_coeff_one_weierstrassExp : IsUnit (coeff 1 (uSer g2 g3)) := by
  rw [uSer_coeff_one]
  exact isUnit_one
end Field
section Map
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K)
end Map
end ReciprocityTheory.ChartRestriction.L1


