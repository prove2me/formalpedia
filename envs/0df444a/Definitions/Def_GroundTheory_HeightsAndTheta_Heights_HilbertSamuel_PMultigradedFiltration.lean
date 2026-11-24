-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:49.513352+00:00
-- url     : https://prove2.me/theorems/c517cf75-d02c-49b5-b984-1bc6ae7bed9c
-- title:
--   PMultigraded Filtration
-- statement:
--   Definitions and structural lemmas for PMultigraded Filtration, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
namespace MultigradedFiltration
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
def degZ (b : K → ℕ) : K → ℤ := fun k => (b k : ℤ)
section Graded
variable [DecidableEq (K → ℤ)] [DirectSum.Decomposition piece]
def IsGradedSub (piece : (K → ℤ) → Submodule F M) [DirectSum.Decomposition piece]
    (N : Submodule (MRing ι F) M) : Prop :=
  ∀ y ∈ N, ∀ m, (DirectSum.decompose piece y m : M) ∈ N
end Graded
section Chain
variable [DecidableEq (K → ℤ)] [DirectSum.Decomposition piece]
end Chain
end MultigradedFiltration
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


