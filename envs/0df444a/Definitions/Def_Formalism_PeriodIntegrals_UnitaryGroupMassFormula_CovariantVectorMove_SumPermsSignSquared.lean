-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:58:03.187077+00:00
-- url     : https://prove2.me/theorems/312a9181-64fc-4367-b302-162ad847b118
-- title:
--   Sum Perms Sign Squared
-- statement:
--   Definitions and structural lemmas for Sum Perms Sign Squared, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermsSignSquared.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
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
section Vec
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (y : Fin n → A)
  (a : Fin m → Fin n) (b : Fin (m + 1) → Fin n) (w : ℂ)
def Fv (p : ℕ) (τ : Equiv.Perm (Fin (m + 1))) (σ : Equiv.Perm (Fin m)) (q : Fin (m + 1)) : A :=
  if (q : ℕ) = p then y (b (τ q))
  else if (q : ℕ) < p then Tm E (w - 1 - ((q : ℕ) : ℂ)) (extN (a ∘ σ) (b 0) q) (b (τ q))
  else Tm E (w - (((q : ℕ) - 1 : ℕ) : ℂ)) (extN (a ∘ σ) (b 0) ((q : ℕ) - 1)) (b (τ q))
def Pv (p : ℕ) (τ : Equiv.Perm (Fin (m + 1))) : A :=
  ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : A) * (List.ofFn (Fv E y a b w p τ σ)).prod
def Mv (p : ℕ) : A := ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * Pv E y a b w p τ
omit [Algebra ℂ A] in

def symV (x c d : Fin n) : A := (if x = d then y c else 0) + (if x = c then y d else 0)
end Vec
end PI.UnitaryGroupMassFormula.QmMove


