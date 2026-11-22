-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
-- name    : Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:55.6518+00:00
-- url     : https://prove2.me/theorems/5678964a-8f2e-4208-b14c-4121dbc4c0a2
-- title:
--   Harmonic Decomposition Holds
-- statement:
--   Definitions and structural lemmas for Harmonic Decomposition Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
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
namespace Formalism.CountingSumsFrames
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
def cP (K : Type) [Field K] (M l : ℕ) : K :=
  (-1 : K) ^ l / ((M.choose l : ℕ) : K) * (((l.factorial : ℕ) : K)⁻¹ * ((l.factorial : ℕ) : K)⁻¹)
end Har2
open Har2
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
end Har2
end Formalism.CountingSumsFrames


