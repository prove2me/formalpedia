-- Prove2me | solution 1 for AutomorphicForm.WeylIntegrable.dilate_finPart_of_snd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/0253f9b2-8cb4-5a5a-b18a-0aae8b837343

import Definitions.Def_AutomorphicForm_WeylSelectors
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WeylIntegrable_dilate_finPart_of_snd_eq

open NumberField NumberField.AdelicBox IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical Pointwise

namespace AutomorphicForm
namespace WeylIntegrable
p2m_export "AutomorphicForm.WeylIntegrable" "yUnit BigFin one_lt_valued_of_bigFin selY selY_snd selRel dilate coe_dilate finPart"
namespace DilateOfFinitePart
p2m_open "AutomorphicForm.WeylIntegrable AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "HOS" => HeightOneSpectrum (𝓞 F)

private theorem fa_mul_apply (a b : 𝔸f) (v : HOS) : (a * b) v = a v * b v := rfl

private theorem mem_integralFiniteAdeles_iff' (t : 𝔸f) :
    t ∈ integralFiniteAdeles (𝓞 F) F ↔ ∀ v, Valued.v (t v) ≤ 1 := Iff.rfl

private theorem valued_ne_zero_of_unit (y : (𝔸f)ˣ) (v : HOS) : Valued.v ((y : 𝔸f) v) ≠ 0 := by
  intro h
  have h1 : Valued.v (((y : 𝔸f) * ((y⁻¹ : (𝔸f)ˣ) : 𝔸f)) v) = 1 := by rw [Units.mul_inv]; exact map_one _
  rw [fa_mul_apply, map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

private theorem mem_dilate_iff (y : (𝔸f)ˣ) (t : 𝔸f) :
    t ∈ dilate F y ↔ ∀ v, Valued.v (t v) ≤ Valued.v ((y : 𝔸f) v) := by
  rw [← SetLike.mem_coe, coe_dilate, Set.mem_smul_set]
  constructor
  · rintro ⟨s, hs, rfl⟩ v
    rw [smul_eq_mul, fa_mul_apply, map_mul]
    exact mul_le_of_le_one_right' ((mem_integralFiniteAdeles_iff' F s).mp hs v)
  · intro h
    refine ⟨((y⁻¹ : (𝔸f)ˣ) : 𝔸f) * t, (mem_integralFiniteAdeles_iff' F _).mpr fun v => ?_, ?_⟩
    · rw [fa_mul_apply, map_mul]
      have hy := valued_ne_zero_of_unit F y v
      have hyv : (y : 𝔸f) v * ((y⁻¹ : (𝔸f)ˣ) : 𝔸f) v = 1 := by rw [← fa_mul_apply, Units.mul_inv]; rfl
      have hinv : Valued.v (((y⁻¹ : (𝔸f)ˣ) : 𝔸f) v) = (Valued.v ((y : 𝔸f) v))⁻¹ := by
        rw [← inv_eq_of_mul_eq_one_right hyv, map_inv₀]
      rw [hinv]
      calc (Valued.v ((y : 𝔸f) v))⁻¹ * Valued.v (t v) ≤ (Valued.v ((y : 𝔸f) v))⁻¹ * Valued.v ((y : 𝔸f) v) :=
            mul_le_mul' le_rfl (h v)
        _ = 1 := inv_mul_cancel₀ hy
    · show (y : 𝔸f) * (((y⁻¹ : (𝔸f)ˣ) : 𝔸f) * t) = t
      rw [← mul_assoc, Units.mul_inv, one_mul]

private theorem valued_selY_snd (a : InfiniteAdeleRing F) (b : 𝔸f) (v : HOS) :
    Valued.v ((selY F a b).2 v) = max 1 (Valued.v (b v)) := by
  rw [selY_snd]
  by_cases h : BigFin F b v
  · rw [if_pos h, max_eq_right (one_lt_valued_of_bigFin F h).le]
  · rw [if_neg h, map_one, max_eq_left ((mem_adicCompletionIntegers _ _ _).mp (not_not.mp h))]

end AutomorphicForm.WeylIntegrable.DilateOfFinitePart

open _root_.AutomorphicForm.WeylIntegrable _root_.P2MW.S_AutomorphicForm_WeylIntegrable_dilate_finPart_of_snd_eq.AutomorphicForm.WeylIntegrable AutomorphicForm.WeylIntegrable.DilateOfFinitePart in

theorem solution (F : Type) [Field F] [NumberField F]
    (x y : NumberField.AdeleRing (NumberField.RingOfIntegers F) F) (hy2 : y.2 = x.2) :
    dilate F (finPart F (yUnit (selRel F y.1 y.2))) = dilate F (finPart F (yUnit (selRel F x.1 x.2))) := by
  ext r
  rw [mem_dilate_iff, mem_dilate_iff]
  have key : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (((finPart F (yUnit (selRel F y.1 y.2)) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) =
        Valued.v (((finPart F (yUnit (selRel F x.1 x.2)) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) :=
    fun v => by
      show Valued.v ((selY F y.1 y.2).2 v) = Valued.v ((selY F x.1 x.2).2 v)
      rw [valued_selY_snd, valued_selY_snd, hy2]
  simp only [key]

end S_AutomorphicForm_WeylIntegrable_dilate_finPart_of_snd_eq
end P2MW
export P2MW.S_AutomorphicForm_WeylIntegrable_dilate_finPart_of_snd_eq (solution)
