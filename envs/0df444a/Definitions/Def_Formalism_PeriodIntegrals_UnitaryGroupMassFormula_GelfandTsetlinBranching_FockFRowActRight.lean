-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:12.790854+00:00
-- url     : https://prove2.me/theorems/a0a0b88e-c51f-492c-82cd-f4618207b797
-- title:
--   Fock FRow Act Right
-- statement:
--   Definitions and structural lemmas for Fock FRow Act Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FockFRowActRight.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
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
def iotaC (R : Type) [CommRing R] (n k : ℕ) (Y : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + k)) (Fin (n + k)) R :=
  Matrix.reindexAlgEquiv R R finSumFinEquiv (Matrix.fromBlocks Y 0 0 1)
open Formalism.REAL (fockF)
def fct {σ : Type} (m : σ →₀ ℕ) : ℂ := ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ)
end PI.WGB


