-- Prove2me | Definitions.Def_row23_rh_supp_RH65000EvaluatorChunks
-- name    : row23_rh_supp_RH65000EvaluatorChunks
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:20:12.915809+00:00
-- url     : https://prove2.me/theorems/5aea59e8-7a36-4e78-940c-f590fbb9acf3
-- title:
--   Row 23 RH support: RH65000EvaluatorChunks
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
set_option autoImplicit false
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH65000ExtendedSlab

/-- A long evaluator run can be checked as two consecutive shorter runs. -/
theorem runO_add (c : Cfg) (o : OCfg) (m n : Nat) (s : StO) :
    runO c o (m + n) s = runO c o n (runO c o m s) := by
  induction m generalizing s with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
      simpa only [Nat.succ_add, runO] using ih (stepO c o s)

end RH65000ExtendedSlab
#print axioms RH65000ExtendedSlab.runO_add


