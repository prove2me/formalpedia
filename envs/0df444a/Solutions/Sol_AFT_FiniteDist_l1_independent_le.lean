-- Prove2me | solution 1 for AFT.FiniteDist.l1_independent_le
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T09:33:55.769575+00:00
-- url     : https://prove2.me/submissions/d12d40e6-0283-4def-b384-018d1cd06f74

import Definitions.Def_InfoLossLAR_Native_AFT_FiniteConcentration
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic
import Theorems.Thm_AFT_FiniteDist_l1_independent_fin_le
import Theorems.Thm_AFT_FiniteDist_l1_map_le

namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.joint
end AFT.FiniteDist.joint
section



/-! # Product samplers with coordinate-dependent output alphabets -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

 

 

 

 

 set_option maxRecDepth 8192
theorem _root_.AFT.FiniteDist.__p2m_proof_3ca47dfd623eb623fb0f {Index State : Type*} [Fintype Index] [DecidableEq Index] [Fintype State]
    (first second : Index → FiniteDist State) :
    (∑ word,|(independent first).weight word-(independent second).weight word|)≤
      ∑ i,∑ point,|(first i).weight point-(second i).weight point| := by
  let e := Fintype.equivFin Index
  let ew : (Fin (Fintype.card Index) → State) ≃ (Index → State) :=
    Equiv.arrowCongr e.symm (Equiv.refl State)
  have he (law : Index → FiniteDist State) : independent law=
      (independent (fun i => law (e.symm i))).map ew := by
    ext word
    rw [map_equiv_weight]
    change (∏ i,(law i).weight (word i))=∏ i,(law (e.symm i)).weight (word (e.symm i))
    exact (e.symm.prod_comp (fun i => (law i).weight (word i))).symm
  rw [he first,he second]
  apply (l1_map_le _ _ _).trans
  apply (l1_independent_fin_le _ _ _).trans
  exact le_of_eq (e.symm.sum_comp (fun i => ∑ point,|(first i).weight point-(second i).weight point|))

end
end AFT.FiniteDist

end


set_option maxRecDepth 65536
theorem solution.{u_1,u_2} : (type_of% @_root_.AFT.FiniteDist.__p2m_proof_3ca47dfd623eb623fb0f.{u_1,u_2}) := @_root_.AFT.FiniteDist.__p2m_proof_3ca47dfd623eb623fb0f.{u_1,u_2}
