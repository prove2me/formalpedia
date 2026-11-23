-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfVanish
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfVanish
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:45.20284+00:00
-- url     : https://prove2.me/theorems/81c6df1a-9beb-42cd-a532-b10acfc64dcb
-- title:
--   Submatrix Mul Of Vanish
-- statement:
--   Definitions and structural lemmas for Submatrix Mul Of Vanish, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubmatrixMulOfVanish.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
namespace GlobalTheory.TorsionUnique
variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix]
def HasDeg (deg : Ix → ℕ) (k : ℤ) (X : Matrix Ix Ix R) : Prop :=
  ∀ p q, (deg p : ℤ) ≠ deg q + k → X p q = 0
end GlobalTheory.TorsionUnique


