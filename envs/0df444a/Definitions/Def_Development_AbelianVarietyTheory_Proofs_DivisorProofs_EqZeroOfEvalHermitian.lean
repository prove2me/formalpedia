-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfEvalHermitian
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfEvalHermitian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:23.478056+00:00
-- url     : https://prove2.me/theorems/9df365a8-d2ce-4bea-9387-1e0f691826c6
-- title:
--   Eq Zero Of Eval Hermitian
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Eval Hermitian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfEvalHermitian.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial GlobalTheory.FibLine
namespace GlobalTheory.FibLine
def hermSubst (ab : Fin 2 × Fin 2) : MvPolynomial (Fin 2 × Fin 2) ℂ :=
  !![X (0, 0), X (0, 1) + C Complex.I * X (1, 0); X (0, 1) - C Complex.I * X (1, 0), X (1, 1)] ab.1 ab.2
end GlobalTheory.FibLine


