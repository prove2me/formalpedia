-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:57.134258+00:00
-- url     : https://prove2.me/theorems/3320eefb-0872-4a29-926c-73be30838d1d
-- title:
--   Abs VNe Zero
-- statement:
--   Definitions and structural lemmas for Abs VNe Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/AbsVNeZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LocJacOrd.W.Ar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical
section AbsV
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
theorem absNorm_ne_zero : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast h
theorem absV_mul (x y : Fv F v) : absV v (x * y) = absV v x * absV v y := by
  by_cases hx : x = 0
  · simp [absV, hx]
  by_cases hy : y = 0
  · simp [absV, hy]
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  have hu : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_unzero, WithZero.coe_mul, map_mul]
  simp only [absV, dif_neg hx', dif_neg hy', dif_neg hxy', hu, toAdd_mul,
    zpow_add₀ (absNorm_ne_zero v)]
theorem absV_zero : absV v (0 : Fv F v) = 0 := by simp [absV]
theorem absV_one : absV v (1 : Fv F v) = 1 := by
  have h1 : Valued.v (1 : Fv F v) ≠ 0 := by simp
  have hu : WithZero.unzero h1 = 1 := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_unzero, map_one, WithZero.coe_one]
  simp only [absV, dif_neg h1, hu, toAdd_one, zpow_zero]
def absVHom : Fv F v →*₀ ℝ where
  toFun := absV v
  map_zero' := absV_zero v
  map_one' := absV_one v
  map_mul' := absV_mul v
end AbsV
section Real
end Real
end PI.LocJacOrd.W.Ar
namespace PI.LocJacOrd.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd
end PI.LocJacOrd.W


