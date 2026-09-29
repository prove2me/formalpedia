-- Prove2me | solution 1 for AutomorphicForm.WeylIntegrable.Dy_eq_prod_mul_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/afc16390-8de9-5e9c-8e54-1cc7c9f63657

import Definitions.Def_AutomorphicForm_WeylSelectors
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_AutomorphicForm_WeylIntegrable_finprod_norm_eq_relIndex_dilate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WeylIntegrable_Dy_eq_prod_mul_relIndex
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec"

set_option autoImplicit false

noncomputable section

section BigComponent

open NumberField IsDedekindDomain AutomorphicForm.WeylIntegrable

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

private theorem norm_bigComponent_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) :
    ‖(selY F a b).1 w‖ = max 1 ‖a w‖ := by
  rw [selY_fst]
  by_cases h : BigInf F a w
  · rw [if_pos h, max_eq_right (le_of_lt h)]
  · rw [if_neg h, norm_one, max_eq_left (not_lt.mp h)]

private theorem one_le_valued_bigComponent_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) :
    1 ≤ Valued.v ((selY F a b).2 v) := by
  rw [selY_snd]
  by_cases h : BigFin F b v
  · rw [if_pos h]; exact (one_lt_valued_of_bigFin F h).le
  · rw [if_neg h, map_one]

end BigComponent

section Solution

open NumberField IsDedekindDomain AutomorphicForm.WeylIntegrable

theorem solution (F : Type) [Field F] [NumberField F]
    (x : NumberField.AdeleRing (NumberField.RingOfIntegers F) F) :
    Dy F x = (∏ w : NumberField.InfinitePlace F, (max 1 ‖x.1 w‖) ^ w.mult)
      * ((intLattice F).relIndex (dilate F (finPart F (yUnit (selRel F x.1 x.2)))) : ℝ) := by
  have harch : (∏ w : InfinitePlace F,
        ‖((yUnit (selRel F x.1 x.2) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult)
      = ∏ w : InfinitePlace F, (max 1 ‖x.1 w‖) ^ w.mult :=
    Finset.prod_congr rfl fun w _ => congrArg (fun t : ℝ => t ^ w.mult) (norm_bigComponent_fst F x.1 x.2 w)
  have hfin : (∏ᶠ v : HeightOneSpectrum (𝓞 F),
        ‖((yUnit (selRel F x.1 x.2) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖)
      = ((intLattice F).relIndex (dilate F (finPart F (yUnit (selRel F x.1 x.2)))) : ℝ) :=
    AutomorphicForm.WeylIntegrable.finprod_norm_eq_relIndex_dilate F (finPart F (yUnit (selRel F x.1 x.2)))
      fun v => one_le_valued_bigComponent_snd F x.1 x.2 v
  exact (NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F
    (yUnit (selRel F x.1 x.2))).trans (congrArg₂ (· * ·) harch hfin)

end Solution

end

end S_AutomorphicForm_WeylIntegrable_Dy_eq_prod_mul_relIndex
end P2MW
export P2MW.S_AutomorphicForm_WeylIntegrable_Dy_eq_prod_mul_relIndex (solution)
