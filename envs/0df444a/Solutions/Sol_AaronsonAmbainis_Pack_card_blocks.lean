-- Prove2me | solution 1 for AaronsonAmbainis.Pack.card_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:32.208597+00:00
-- url     : https://prove2.me/submissions/2ae80e3a-f1e9-4edc-a317-afe81245cf20

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Pack_Blocks

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Pack
theorem _root_.solution (k : Finset ι → ℕ) (i : ι) :
    (univ.filter fun b : (Σ S : Finset ι, Fin (k S)) => i ∈ b.1).card
      = ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), k S := by
  rw [Finset.card_filter, Fintype.sum_sigma, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : i ∈ S
  · simp [h]
  · simp [h]
end AaronsonAmbainis.Pack
