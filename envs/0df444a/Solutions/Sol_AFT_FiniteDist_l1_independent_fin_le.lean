-- Prove2me | solution 1 for AFT.FiniteDist.l1_independent_fin_le
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T06:15:56.622033+00:00
-- url     : https://prove2.me/submissions/759a9fa5-d10b-4b64-a9d7-a474b1ae1c55

import Definitions.Def_InfoLossLAR_Native_AFT_FiniteConcentration
import Mathlib
import Theorems.Thm_AFT_FiniteDist_l1_map_le
import Theorems.Thm_AFT_FiniteDist_l1_prod_le
section


/-! # Total variation of actual independent finite products -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [Fintype A] [Fintype B]





set_option maxRecDepth 8192
omit [Fintype B] in
/-- The comparison is for the literal finite product law; all coordinate
errors are summed once. -/
theorem _root_.AFT.FiniteDist.__p2m_proof_0e390d57935aac65c23c (count : ℕ) (first second : Fin count → _root_.AFT.FiniteDist A) :
    (∑ word,|(_root_.AFT.FiniteDist.independent first).weight word-(_root_.AFT.FiniteDist.independent second).weight word|) ≤
      ∑ i,∑ a,|(first i).weight a-(second i).weight a| := by
  induction count with
  | zero => simp only [_root_.AFT.FiniteDist.independent,Fin.prod_univ_zero,sub_self,abs_zero,Finset.sum_const_zero,Fin.sum_univ_zero,le_refl]
  | succ count ih =>
    let tailFirst := _root_.AFT.FiniteDist.independent (fun i : Fin count => first i.succ)
    let tailSecond := _root_.AFT.FiniteDist.independent (fun i : Fin count => second i.succ)
    have hsplit (law : Fin (count+1) → _root_.AFT.FiniteDist A) : _root_.AFT.FiniteDist.independent law=
        ((law 0).prod (_root_.AFT.FiniteDist.independent (fun i : Fin count => law i.succ))).map (Fin.consEquiv (fun _ : Fin (count+1) => A)) := by
      ext word
      rw [_root_.AFT.FiniteDist.map_equiv_weight]
      change (∏ i,(law i).weight (word i))=(law 0).weight (word 0)*∏ i : Fin count,(law i.succ).weight (word i.succ)
      exact Fin.prod_univ_succ _
    rw [hsplit first,hsplit second,Fin.sum_univ_succ]
    apply (_root_.AFT.FiniteDist.l1_map_le _ _ _).trans
    exact (_root_.AFT.FiniteDist.l1_prod_le (first 0) (second 0) tailFirst tailSecond).trans (add_le_add le_rfl (ih _ _))



end
end AFT.FiniteDist

end


set_option maxRecDepth 65536
theorem solution.{u_1} : (type_of% @_root_.AFT.FiniteDist.__p2m_proof_0e390d57935aac65c23c.{u_1}) := @_root_.AFT.FiniteDist.__p2m_proof_0e390d57935aac65c23c.{u_1}
