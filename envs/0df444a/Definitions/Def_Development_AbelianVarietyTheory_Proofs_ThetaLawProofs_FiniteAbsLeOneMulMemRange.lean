-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:41.644003+00:00
-- url     : https://prove2.me/theorems/82665144-6d9e-44ee-85e2-b92b7666fde5
-- title:
--   Finite Abs Le One Mul Mem Range
-- statement:
--   Definitions and structural lemmas for Finite Abs Le One Mul Mem Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FiniteAbsLeOneMulMemRange.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology
namespace GlobalTheory
variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}
def rankOneCurve (Z : Matrix (Fin g) (Fin g) ℂ) (R : Matrix (Fin g) (Fin g) ℝ) (u : Fin g → ℝ)
    (s : ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  of fun i j => Z i j + R i j + s * u i * u j
section Curve
variable {e : Fin g} {Z : Matrix (Fin g) (Fin g) ℂ} (hZs : Z.IsSymm) (hZe : ∀ i, Z i e = 0)
  (hZ : ∀ u : Fin g → ℝ, u e = 1 → ∀ y : ℝ, 0 < y →
    (Z.map Complex.im + y • vecMulVec u u).PosDef)
end Curve
end GlobalTheory


