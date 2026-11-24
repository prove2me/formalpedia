-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:48.912337+00:00
-- url     : https://prove2.me/theorems/1d640f60-ca53-4e5c-b050-1305200a618a
-- title:
--   PContract A
-- statement:
--   Definitions and structural lemmas for PContract A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractA.lean

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
def reIx {P Q : Type} (e : P ≃ Q) (ξ : TV n M P) : TV n M Q := fun I => ξ (I ∘ e)
def unc {A B : Type} (f : TV n (TV n M A) B) : TV n M (A ⊕ B) := fun I => f (I ∘ Sum.inr) (I ∘ Sum.inl)
def cur {A B : Type} (g : TV n M (A ⊕ B)) : TV n (TV n M A) B := fun J K => g (Sum.elim K J)
def splitE (m n : ℕ) (h : n ≤ m) : Fin m ≃ Fin (m - n) ⊕ Fin n where
  toFun i := if hi : (i : ℕ) < n then Sum.inr ⟨i, hi⟩ else Sum.inl ⟨i - n, by omega⟩
  invFun := Sum.elim (fun j => ⟨j + n, by omega⟩) (fun j => ⟨j, by omega⟩)
  left_inv i := by
    by_cases hi : (i : ℕ) < n
    · simp [hi]
    · simp only [hi, dite_false, Sum.elim_inl]
      ext; simp; omega
  right_inv x := by
    rcases x with j | j
    · simp
    · simp [j.2]
end PositivityTheory.Rg.Cz.CtrX
end


