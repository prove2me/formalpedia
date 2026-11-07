-- Prove2me | solution 1 for AaronsonAmbainis.Dual.cover_iff_packing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:35:08.345256+00:00
-- url     : https://prove2.me/submissions/10d1fa6c-988d-41a4-8adf-143d28a56816

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
import Theorems.Thm_AaronsonAmbainis_Dual_packing_le_of_cover
import Theorems.Thm_AaronsonAmbainis_Dual_exists_cover


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (t : Finset ι → ℝ) (K : ℝ) :
    (∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K) ↔
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ K ∧ ∀ S : Finset ι, t S ≤ ∑ i ∈ S, a i :=
  ⟨exists_cover t K, fun ⟨a, ha0, haK, hcov⟩ κ hκ hload =>
    packing_le_of_cover t K a ha0 haK hcov κ hκ hload⟩
end AaronsonAmbainis.Dual
