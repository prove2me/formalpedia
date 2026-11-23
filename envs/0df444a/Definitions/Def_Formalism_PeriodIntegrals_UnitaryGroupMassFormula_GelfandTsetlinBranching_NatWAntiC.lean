-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_NatWAntiC
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_NatWAntiC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:08:19.311145+00:00
-- url     : https://prove2.me/theorems/7704d5ce-7fb6-469b-b6f9-1a4fe305d88b
-- title:
--   Nat WAnti C
-- statement:
--   Definitions and structural lemmas for Nat WAnti C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/NatWAntiC.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_TransposeConjComm
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
open Formalism.REAL (fockF)
def veC (n : ℕ) (mu : DomWeight n) (g : GL (Fin n) ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  sqAct ℂ n mu g (extremal ℂ n mu)
def vfC (n : ℕ) (lam : DomWeight (n + 1)) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (g : GL (Fin n) ℂ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ :=
  sqAct ℂ (n + 1) lam (PI.embGL ℂ n (n + 1) rfl g) f
end PI.WGB


