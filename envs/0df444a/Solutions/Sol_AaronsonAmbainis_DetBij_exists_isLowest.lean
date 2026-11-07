-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.exists_isLowest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:30:39.822199+00:00
-- url     : https://prove2.me/submissions/b23acad8-ff08-4219-901c-86e6aeaa1892

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (q : MvPolynomial ι ℤ) (hq : q ≠ 0) : ∃ m, IsLowest q m := by
  have hne : q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun h => hq (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨m, hm, hmin⟩ :=
    Finset.exists_min_image q.support (fun m : ι →₀ ℕ => ∑ i, m i) hne
  exact ⟨m, hm, hmin⟩
end AaronsonAmbainis.DetBij
