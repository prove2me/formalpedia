-- Prove2me | solution 1 for AaronsonAmbainis.Dual.massSet_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:20.395628+00:00
-- url     : https://prove2.me/submissions/28ca2891-c99f-49a3-bc08-b2e7602b1570

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets
import Theorems.Thm_AaronsonAmbainis_Dual_massSet_isClosed

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (K : ℝ) : IsCompact (massSet ι K) := by
  have hsub : massSet ι K ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) K) := by
    intro a ha i _
    exact ⟨ha.1 i,
      le_trans (Finset.single_le_sum (fun j _ => ha.1 j) (Finset.mem_univ i)) ha.2⟩
  exact IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc)
    (massSet_isClosed K) hsub
end AaronsonAmbainis.Dual
