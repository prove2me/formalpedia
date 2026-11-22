-- Prove2me | Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormMul
-- name    : Formalism_NormUnitaryBounds_DetPolynomialWeights_NormMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:08:31.635027+00:00
-- url     : https://prove2.me/theorems/74ecd08a-c7f2-4003-a7fd-e33f539896f6
-- title:
--   Norm Mul
-- statement:
--   Definitions and structural lemmas for Norm Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
namespace Formalism.NormUnitaryCountingLemmas
namespace NMul
def Dc {N n : ℕ} (ν : Fin N → ℕ) (c : Fin N × Fin n →₀ ℕ) : ℝ :=
  ∏ j, ((blockDeg c j).choose (ν j) : ℝ)
def Pc {N n : ℕ} (c a : Fin N × Fin n →₀ ℕ) : ℝ :=
  ∏ j, ∏ k, ((c (j, k)).choose (a (j, k)) : ℝ)
end NMul
end Formalism.NormUnitaryCountingLemmas


