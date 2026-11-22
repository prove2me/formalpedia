-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal
-- name    : Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:59.256544+00:00
-- url     : https://prove2.me/theorems/af12f083-3c9b-4668-858f-f4d8641fe1d8
-- title:
--   TTotal
-- statement:
--   Definitions and structural lemmas for TTotal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
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
open Finset
namespace Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
namespace extendedWeightWeylDimension
def star {n : ℕ} (la : Fin n → ℤ) : Fin n → ℤ := fun m => -(extW la (n - 1 - m.val))
def _root_.Formalism.InvariantFactorPaths.BranchingDimensions.Letters.twStep (D : Letters) (i : ℕ) (x y : Fin D.k → ℤ) : Prop :=
  Dom D.k (extW y) ∧
  (D.vec i = true → HStrip D.k (extW x) (extW y)) ∧
  (D.vec i = false → HStrip D.k (extW y) (extW x)) ∧
  (i ≤ D.n0 → D.vec i = true → wsize D.k (extW y) - wsize D.k (extW x) = D.B i) ∧
  (i ≤ D.n0 → D.vec i = false → wsize D.k (extW x) - wsize D.k (extW y) = D.B i) ∧
  (∀ m, m < i - D.n0 → extW y m = D.be)
def _root_.Formalism.InvariantFactorPaths.BranchingDimensions.Letters.twGood (D : Letters) (j : ℕ) (x : Fin D.k → ℤ) : Prop :=
  Dom D.k (extW x) ∧ extW x 0 ≤ ((∑ l ∈ Icc 1 (min j D.n0), D.B l : ℕ) : ℤ) ∧
    ∀ m, m < j - D.n0 → extW x m = D.be
def _root_.Formalism.InvariantFactorPaths.BranchingDimensions.Letters.twG (D : Letters) (j : ℕ) (x : Fin D.k → ℤ) : ℝ :=
  weylDim (D.k - (j - D.n0)) (fun l => extW x (l + (j - D.n0)))
def _root_.Formalism.InvariantFactorPaths.BranchingDimensions.Letters.twC (D : Letters) (i : ℕ) : ℝ :=
  if i ≤ D.n0 then ((D.B i + D.k - 1).choose (D.k - 1) : ℝ) else 1
def rho (D : Letters) (nu : ℕ → Fin D.k → ℤ) : D.Stages := fun i => nu i.val
end extendedWeightWeylDimension
open extendedWeightWeylDimension
end Formalism.InvariantFactorPaths.BranchingDimensions


