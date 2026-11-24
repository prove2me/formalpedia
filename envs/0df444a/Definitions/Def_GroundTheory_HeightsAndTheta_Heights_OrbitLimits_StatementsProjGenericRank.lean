-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjGenericRank
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjGenericRank
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:27.739071+00:00
-- url     : https://prove2.me/theorems/b17edfb0-fc5b-4981-bed0-7261cd3fddf5
-- title:
--   Statements Proj Generic Rank
-- statement:
--   Definitions and structural lemmas for Statements Proj Generic Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsProjGenericRank.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
def ProjGenericRank.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsClosed V → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ j, ∀ᵐ u, u ∈ (BV.chart j).target → (BV.chart j).symm u ∉ projRegular R Ψ BV →
      ∃ p : (k : K) → ι k,
        (∀ k, R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm u).1 ⟨k, p k⟩ ≠ 0) ∧
        Module.finrank ℂ (LinearMap.range (fderiv ℂ
          (fun y => ReciprocityTheory.ChartRestriction.G.Geo.affCoord p
            (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm y).1)) u :
            (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))) < n
end GroundTheory.Heights₂.Heights.Targets


