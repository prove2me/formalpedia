-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SchurFock
-- name    : Formalism_PeriodIntegrals_SchurFock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:49.615666+00:00
-- url     : https://prove2.me/theorems/b4d2b92f-4925-4c7b-8e29-37846daeb799
-- title:
--   Schur Fock
-- statement:
--   Definitions and structural lemmas for Schur Fock, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SchurFock.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
open Formalism.BasicNotions MvPolynomial
def SchurFock : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N), ∀ s ∈ nablaSq ℂ N lam,
    (∀ x ∈ Matrix.unitaryGroup (Fin N) ℂ, ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) s‖ ≤ 1) →
    (normFock lam s s).re ≤ (Module.finrank ℂ (delSq ℂ N lam) : ℝ)
end PI


