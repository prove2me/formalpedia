-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:08:27.66677+00:00
-- url     : https://prove2.me/theorems/8b7bfe2a-b559-4e83-bf32-185fc78a2226
-- title:
--   DSFdeg
-- statement:
--   Definitions and structural lemmas for DSFdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/DSFdeg.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.QuantumDeterminants
open Formalism.REAL
def fdNum {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |lam a - lam b|
def fdFull {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  ∏ a : Fin n, ∏ b : Fin n, (if a = b then 1 else |lam a - lam b|)
end Formalism.QuantumDeterminants


