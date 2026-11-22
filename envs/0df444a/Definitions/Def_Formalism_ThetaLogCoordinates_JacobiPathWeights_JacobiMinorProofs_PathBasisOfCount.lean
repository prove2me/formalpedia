-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:46.179398+00:00
-- url     : https://prove2.me/theorems/d47c12bf-7488-402b-9a94-07be7adf406b
-- title:
--   Path Basis Of Count
-- statement:
--   Definitions and structural lemmas for Path Basis Of Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathBasisOfCount.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
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
namespace MinorDeterminantBasis
section Abstract
variable {σ X : Type} [Fintype X] [DecidableEq X]
def cmat (m : X → σ →₀ ℕ) (F : X → MvPolynomial σ ℤ) : Matrix X X ℤ :=
  Matrix.of fun x y => coeff (m y) (F x)
end Abstract
def expSet (n N : ℕ) (B : ℕ → ℕ) : Set (ℕ × Fin n →₀ ℕ) :=
  {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then B i else 0}
end MinorDeterminantBasis
open MinorDeterminantBasis
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


