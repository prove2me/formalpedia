-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_EagonNorthcottZ
-- name    : Formalism_PeriodIntegrals_EagonNorthcottZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:49.097252+00:00
-- url     : https://prove2.me/theorems/85e62728-446b-460a-b508-3e9326a6690a
-- title:
--   Eagon Northcott Z
-- statement:
--   Definitions and structural lemmas for Eagon Northcott Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/EagonNorthcottZ.lean

import Definitions.Def_Formalism_PeriodIntegrals_EagonNorthcott
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
open EagonNorthcott in

def EagonNorthcottZ : Prop :=
  ∀ D a : ℕ, ∃ (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ) (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)),
    Shape D a n e C ∧ Resolves (MvPolynomial.X : Fin D → MvPolynomial (Fin D) ℤ) a e C
end PI


