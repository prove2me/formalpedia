-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:08.542162+00:00
-- url     : https://prove2.me/theorems/2e650664-2ab0-4bce-bce2-1c3590bacfc5
-- title:
--   Prod Mk Pt A
-- statement:
--   Definitions and structural lemmas for Prod Mk Pt A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ProdMkPtA.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
def mStarA (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) : Fin (n + 1) × Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v =>
    Fin.lastCases (Fin.lastCases (ν (Fin.last n)) (fun k => ν (Fin.castSucc k) - kap k) v.2)
      (fun a => Fin.lastCases 0 (fun k => if k = a then kap a else 0) v.2) v.1
def IsDPtA (x : Fin (n + 1) × Fin (n + 1) → ℂ) : Prop :=
  ∀ a j : Fin (n + 1), a.val < n → a ≠ j → x (a, j) = 0
def kapA (lam : DomWeight (n + 1)) (mu : DomWeight n) (a : Fin n) : ℕ := (mu.w a - lam.detShift).toNat
def mkPtA (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) : Fin (n + 1) × Fin (n + 1) → ℂ :=
  fun v => Fin.lastCases (z v.2) (fun a => Fin.lastCases 0 (fun k => if k = a then dv a else 0) v.2) v.1
end PI.WGB


