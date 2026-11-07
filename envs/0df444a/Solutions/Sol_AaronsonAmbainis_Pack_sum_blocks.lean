-- Prove2me | solution 1 for AaronsonAmbainis.Pack.sum_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:32.959481+00:00
-- url     : https://prove2.me/submissions/40c83b8b-cc25-4f94-ba5d-45f4d034d35e

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Pack_Blocks

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Pack
theorem _root_.solution (k : Finset ι → ℕ) (g : Finset ι → ℝ) :
    ∑ b : (Σ S : Finset ι, Fin (k S)), g b.1 = ∑ S, (k S : ℝ) * g S := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun S _ => ?_
  show ∑ _y : Fin (k S), g S = (k S : ℝ) * g S
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
end AaronsonAmbainis.Pack
