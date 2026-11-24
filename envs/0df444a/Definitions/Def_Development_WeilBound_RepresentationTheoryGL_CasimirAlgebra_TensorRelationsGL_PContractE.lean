-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:04.760301+00:00
-- url     : https://prove2.me/theorems/f5e25ee5-61fd-4feb-9409-f9427a21d46c
-- title:
--   PContract E
-- statement:
--   Definitions and structural lemmas for PContract E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractE.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
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
namespace PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
def omcGlue {m : ℕ} (j : Fin m) (b : Fin n) (R : {p // p ≠ j} → Fin n) : Fin m → Fin n :=
  fun p => if h : p = j then b else R ⟨p, h⟩
def omcEquiv {m : ℕ} (j : Fin m) : (Fin m → Fin n) ≃ Fin n × ({p // p ≠ j} → Fin n) where
  toFun J := (J j, fun p => J p.1)
  invFun x := omcGlue j x.1 x.2
  left_inv J := by
    funext p
    by_cases h : p = j
    · subst h; simp [omcGlue]
    · simp [omcGlue, h]
  right_inv x := by
    rcases x with ⟨b, R⟩
    simp only [omcGlue, dite_true, Prod.mk.injEq, true_and]
    funext p
    simp [p.2]
end PositivityTheory.Rg.Cz.CtrX
end


