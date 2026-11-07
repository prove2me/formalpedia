-- Prove2me | solution 1 for AaronsonAmbainis.Dual.empty_nonpos_of_packing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:35:34.110951+00:00
-- url     : https://prove2.me/submissions/66882480-18b1-4717-a5e1-655b023f4593

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
import Theorems.Thm_AaronsonAmbainis_Dual_exists_cover
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (t : Finset ι → ℝ) (K : ℝ)
    (hpack : ∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K) : t ∅ ≤ 0 := by
  obtain ⟨a, -, -, h⟩ := exists_cover t K hpack
  simpa using h ∅
end AaronsonAmbainis.Dual
