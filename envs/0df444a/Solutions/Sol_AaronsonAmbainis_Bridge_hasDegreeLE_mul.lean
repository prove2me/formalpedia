-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:41:11.755786+00:00
-- url     : https://prove2.me/submissions/1b154afd-bda2-44e8-a83d-c019557071bc

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_const
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_smul
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_sum
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_chi
import Theorems.Thm_AaronsonAmbainis_Bridge_card_symmDiff_le
import Theorems.Thm_AaronsonAmbainis_Bridge_chi_mul_chi
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_mono


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f g : Cube ι → ℝ} {d e : ℕ} (hf : HasDegreeLE f d)
    (hg : HasDegreeLE g e) : HasDegreeLE (fun x => f x * g x) (d + e) := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  have h1 : (fun x => f x * g x)
      = fun x => ∑ S : Finset ι, ∑ T : Finset ι, (a S * b T) * chi (symmDiff S T) x := by
    funext x
    rw [hfa x, hgb x, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
    rw [← chi_mul_chi]
    ring
  rw [h1]
  refine hasDegreeLE_sum _ (fun S _ => hasDegreeLE_sum _ (fun T _ => ?_))
  by_cases hS : d < S.card
  · have h0 : (fun x => a S * b T * chi (symmDiff S T) x) = fun _ => 0 := by
      funext x
      rw [ha S hS]
      ring
    rw [h0]
    exact hasDegreeLE_const 0 _
  · by_cases hT : e < T.card
    · have h0 : (fun x => a S * b T * chi (symmDiff S T) x) = fun _ => 0 := by
        funext x
        rw [hb T hT]
        ring
      rw [h0]
      exact hasDegreeLE_const 0 _
    · refine hasDegreeLE_smul _ (hasDegreeLE_mono (hasDegreeLE_chi _) ?_)
      exact (card_symmDiff_le S T).trans (Nat.add_le_add (not_lt.mp hS) (not_lt.mp hT))
end AaronsonAmbainis.Bridge
