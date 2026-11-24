-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:02.084351+00:00
-- url     : https://prove2.me/theorems/7a7945ac-b503-486f-b735-59d39c83a7b1
-- title:
--   PTrans All B
-- statement:
--   Definitions and structural lemmas for PTrans All B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllB.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one


set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  (q : P → Prop) [DecidablePred q]
def merge (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) : P → Fin n :=
  fun p => if h : q p then J ⟨p, h⟩ else I ⟨p, h⟩
omit [Fintype P] [DecidableEq P] in
theorem merge_left (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // q p}) :
    merge q J I x.1 = J x := by simp [merge, x.2]
omit [Fintype P] [DecidableEq P] in
theorem merge_right (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // ¬ q p}) :
    merge q J I x.1 = I x := by simp [merge, x.2]
def spl : TV n M P ≃ₗ[ℂ] TV n (TV n M {p // ¬ q p}) {p // q p} where
  toFun F J I := F (merge q J I)
  invFun G K := G (fun x => K x.1) (fun x => K x.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv F := by
    funext K
    show F (merge q _ _) = F K
    congr 1
    funext p
    by_cases h : q p <;> simp [merge, h]
  right_inv G := by
    funext J I
    show G (fun x => merge q J I x.1) (fun x => merge q J I x.1) = G J I
    congr 1 <;> funext x
    · exact merge_left q J I x
    · exact merge_right q J I x
end PositivityTheory.Rg.Cz.TA
end


