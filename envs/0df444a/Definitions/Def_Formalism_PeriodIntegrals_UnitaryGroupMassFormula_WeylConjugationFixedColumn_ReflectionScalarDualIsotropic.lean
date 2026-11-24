-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:25:58.170616+00:00
-- url     : https://prove2.me/theorems/07543809-0162-4487-982d-f28f5d37e68f
-- title:
--   Reflection Scalar Dual Isotropic
-- statement:
--   Definitions and structural lemmas for Reflection Scalar Dual Isotropic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylConjugationFixedColumn/ReflectionScalarDualIsotropic.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace PI.IsotropicReflections
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {k r : ℕ}
def sw (l : Fin r) (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if p = eI k r l then esI k r l else if p = esI k r l then eI k r l else p
def al (l : Fin r) (c : ℂ) (p : Fin (2 * r + k + 1)) : ℂ :=
  if p = eI k r l then c else if p = esI k r l then (star c)⁻¹ else 1
section G
variable (l : Fin r) (g : Mx k r) (hg : g ∈ Glev k r l.succ)
include hg
end G
end PI.IsotropicReflections


