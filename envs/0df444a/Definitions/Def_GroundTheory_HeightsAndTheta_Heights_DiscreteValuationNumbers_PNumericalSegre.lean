-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:09.615552+00:00
-- url     : https://prove2.me/theorems/82f72b31-c4fb-4882-aa0b-9a13cb131555
-- title:
--   PNumerical Segre
-- statement:
--   Definitions and structural lemmas for PNumerical Segre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace NumericalSegreProof
section Combinatorics
end Combinatorics
section Lists
variable {K : Type*} [DecidableEq K]
end Lists
def segreSide {K : Type*} [DecidableEq K] {ι : K → Type*} (F : Type*) [Field F]
    (P : Ideal (MRing ι F)) {i : ℕ} (x : Fin i → K → ℤ) (n : ℕ) (Y : List (K → ℤ)) : ℤ :=
  if i - 1 ≤ n then
    ∑ α ∈ Finset.Nat.antidiagonalTuple i (n - (i - 1)), intNumL F P (rootList x α ++ Y)
  else 0
end NumericalSegreProof
end
end GroundTheory.Heights₂.Heights.NumbersDVR


