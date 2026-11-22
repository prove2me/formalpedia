-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PairingAdjointLaplacianHolds
-- name    : Formalism_PolynomialDimension_MultinomialDepth_PairingAdjointLaplacianHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:36.541327+00:00
-- url     : https://prove2.me/theorems/a7e727c7-cb7b-4740-a473-2b5ce4f44a7c
-- title:
--   Pairing Adjoint Laplacian Holds
-- statement:
--   Definitions and structural lemmas for Pairing Adjoint Laplacian Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PairingAdjointLaplacianHolds.lean

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.CountingSumsFrames
section Gen
variable (K : Type) [Field K] (k : ℕ)
def eulX_har (f : PolXY K k) : PolXY K k := ∑ i : Fin k, X (Sum.inl i) * pderiv (Sum.inl i) f
def eulY (f : PolXY K k) : PolXY K k := ∑ i : Fin k, X (Sum.inr i) * pderiv (Sum.inr i) f
variable {K k}
end Gen
section Gen2
variable {K : Type} [Field K] {k : ℕ}
end Gen2
section Fis
variable {K : Type} [Field K] {k : ℕ}
end Fis
section Can
variable {K : Type} [Field K] {k : ℕ}
end Can
end Formalism.CountingSumsFrames


