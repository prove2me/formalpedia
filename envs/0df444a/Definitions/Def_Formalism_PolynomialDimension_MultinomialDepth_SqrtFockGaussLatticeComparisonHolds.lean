-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
-- name    : Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:41.973816+00:00
-- url     : https://prove2.me/theorems/36751b55-73dd-4511-a725-d76a79d114a5
-- title:
--   Sqrt Fock Gauss Lattice Comparison Holds
-- statement:
--   Definitions and structural lemmas for Sqrt Fock Gauss Lattice Comparison Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
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
namespace Har4
def wXY (k : ℕ) : XY k → ℕ × ℕ := Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1))
def xMul {k : ℕ} (m : XY k →₀ ℕ) : ℕ := Nat.multinomial Finset.univ (fun i : Fin k => m (Sum.inl i))
def yMul {k : ℕ} (m : XY k →₀ ℕ) : ℕ := Nat.multinomial Finset.univ (fun i : Fin k => m (Sum.inr i))
section std
variable {K : Type} [Field K] [CharZero K] {k A B : ℕ} (R : Subring K)
end std
section deg
variable {K : Type} [Field K] {k : ℕ}
end deg
end Har4
end Formalism.CountingSumsFrames


