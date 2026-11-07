-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.mon_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:50.51938+00:00
-- url     : https://prove2.me/submissions/eacec212-2f82-4a21-99b2-7cbf9a6d2ed7

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {φ ψ : Bool → ℝ} {α β : ℝ} (hψ : ∀ b, ψ b = β * φ b + α) (S : Finset ι)
    (x : Cube ι) :
    mon ψ S x
      = ∑ T : Finset ι, if T ⊆ S then β ^ T.card * α ^ (S \ T).card * mon φ T x else 0 := by
  have hpow : S.powerset = univ.filter (fun T => T ⊆ S) := by
    ext T
    simp [Finset.mem_powerset]
  unfold mon
  simp only [hψ]
  rw [Finset.prod_add, hpow, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  split_ifs with hT
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const]
    ring
  · rfl
end AaronsonAmbainis.Bridge
