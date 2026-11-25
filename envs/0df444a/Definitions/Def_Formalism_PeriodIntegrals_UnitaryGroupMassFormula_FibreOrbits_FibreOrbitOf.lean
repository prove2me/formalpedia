-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FibreOrbits_FibreOrbitOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FibreOrbits_FibreOrbitOf
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:10:16.370528+00:00
-- url     : https://prove2.me/theorems/09f295ce-3cd7-5b6d-8bc4-46b647c47df9
-- title:
--   Fibre Orbit Of
-- statement:
--   Definitions and structural lemmas for Fibre Orbit Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FibreOrbits/FibreOrbitOf.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.UnitaryGroupMassFormula.FibOrbAsmW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
def sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩
def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if r ≤ i.val ∧ i.val ≤ r + k ∧ i.val = r + k then -1 else 1
section Group
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Group
end PI.UnitaryGroupMassFormula.FibOrbAsmW


