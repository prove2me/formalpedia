-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:45:20.406805+00:00
-- url     : https://prove2.me/theorems/7e0b6730-d4ae-4624-b3ff-fe42fffcbded
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowFormPermutationSplit/Development.lean

import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.QmRowForm
def doubleRowFormSum {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (x : Fin t → ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin t), ∑ τ : Equiv.Perm (Fin t),
    (((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ) : ℤ) : A) *
      (List.ofFn fun k : Fin t => Tm E (x k) (a (σ k)) (b (τ k))).prod
def DblDec : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin t → Fin n) (u : ℂ),
      doubleRowFormSum E a b (fun k : Fin t => u - (k : ℂ)) = (t.factorial : ℂ) • qminor E a b u
def DblInc : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin t → Fin n) (u : ℂ),
      doubleRowFormSum E a b (fun k : Fin t => u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) =
        (t.factorial : ℂ) • PI.qminorRow E a b u
def DblPerm : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin t → Fin n) (x : Fin t → ℂ) (π : Equiv.Perm (Fin t)),
      doubleRowFormSum E a b (x ∘ π) = doubleRowFormSum E a b x
end PI.UnitaryGroupMassFormula.QmRowForm


