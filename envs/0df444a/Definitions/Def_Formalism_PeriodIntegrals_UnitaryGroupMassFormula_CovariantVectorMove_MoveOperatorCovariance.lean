-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:55:18.864717+00:00
-- url     : https://prove2.me/theorems/f115dd0e-62c6-4875-8191-c14ccfc80b9f
-- title:
--   Move Operator Covariance
-- statement:
--   Definitions and structural lemmas for Move Operator Covariance, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/MoveOperatorCovariance.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
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
namespace PI.UnitaryGroupMassFormula.QmMove
def extN {n m : ℕ} (b : Fin m → Fin n) (d : Fin n) (k : ℕ) : Fin n :=
  if h : k < m then b ⟨k, h⟩ else d
section Cov
variable {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (η : Fin n → A)
  (a : Fin (m + 1) → Fin n) (b : Fin m → Fin n) (w : ℂ)
def Fc (p : ℕ) (τ : Equiv.Perm (Fin (m + 1))) (q : Fin (m + 1)) : A :=
  if (q : ℕ) = p then η (a (τ q))
  else Tm E (w - ((q : ℕ) : ℂ)) (a (τ q)) (extN b (a 0) (if (q : ℕ) < p then (q : ℕ) else (q : ℕ) - 1))
def Nc (p : ℕ) : A := ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * (List.ofFn (Fc E η a b w p τ)).prod
omit [Algebra ℂ A] in

def symC (d x c : Fin n) : A := (if x = d then η c else 0) + (if c = d then η x else 0)
end Cov
end PI.UnitaryGroupMassFormula.QmMove


