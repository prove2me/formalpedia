-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_MemOfProjTwoEqZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_MemOfProjTwoEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:48.909741+00:00
-- url     : https://prove2.me/theorems/d96cbb13-b47c-46ee-901a-1438df5c7800
-- title:
--   Mem Of Proj Two Eq Zero
-- statement:
--   Definitions and structural lemmas for Mem Of Proj Two Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_Hf_add_l
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_Hf_smul_l

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open Complex NumberField
open scoped InnerProductSpace
noncomputable section
namespace Col
variable {E : Type} [Field E] [NumberField E]
section PT
variable (X : PT E) (I : Submodule ℤ (Vsp X.dim))
def Ip : Submodule ℤ (Vsp X.dim) where
  carrier := {x | x ∈ X.L ∧ ∀ a ∈ I, (Hf x a).im = 0}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨X.L.add_mem hx hy, fun a ha => ?_⟩
    rw [Hf_add_l, Complex.add_im, hx' a ha, hy' a ha, add_zero]
  zero_mem' := ⟨X.L.zero_mem, fun a _ => by simp [Hf]⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    refine ⟨X.L.smul_mem c hx, fun a ha => ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℂ c x, Hf_smul_l, Complex.mul_im, hx' a ha]
    simp
variable {X I}
end PT
section Split
variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF}
variable (hI : IsSplit P I)
include hI
end Split
section Lat
variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF}
variable (hI : IsSplit P I)
include hI
end Lat
end Col
end
end ReciprocityTheory.ChartRestriction.G.I2


