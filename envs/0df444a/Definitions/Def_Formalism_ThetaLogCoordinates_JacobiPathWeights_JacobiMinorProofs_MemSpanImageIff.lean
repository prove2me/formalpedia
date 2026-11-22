-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_MemSpanImageIff
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_MemSpanImageIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:30:27.082798+00:00
-- url     : https://prove2.me/theorems/6325dc1d-3d5e-42fc-be74-05840526f80b
-- title:
--   Mem Span Image Iff
-- statement:
--   Definitions and structural lemmas for Mem Span Image Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/MemSpanImageIff.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace SpanImageLemmas
variable {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}
def good (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : ℕ → WithBot ℤ) (M : ℕ → WithTop ℤ) :
    Set (PathIdx n N isVec B) :=
  {x | ∀ i ≤ N, GoodW (θ i) (M i) (x.1.1 i)}
end SpanImageLemmas
open SpanImageLemmas
namespace SpanImageLemmas
variable {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}
end SpanImageLemmas
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


