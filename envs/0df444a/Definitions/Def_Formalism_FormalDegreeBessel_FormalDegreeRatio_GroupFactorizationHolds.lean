-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:08:14.214957+00:00
-- url     : https://prove2.me/theorems/48ef5a71-c573-4fd1-9d84-4b49d30e9d36
-- title:
--   Group Factorization Holds
-- statement:
--   Definitions and structural lemmas for Group Factorization Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
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
namespace Formalism.QuantumDeterminants
def Fm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i a => fvec k r z a i
def Uof (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun c a => if hc : c.val < r then (m * Fm k r z) (eI k r ⟨c.val, hc⟩) a else if c = a then 1 else 0
end Formalism.QuantumDeterminants


