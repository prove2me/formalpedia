-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjMaxRank
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjMaxRank
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:59:59.39791+00:00
-- url     : https://prove2.me/theorems/3c536e81-ebe3-4efc-bf96-2c6fd53bba51
-- title:
--   Statements Proj Max Rank
-- statement:
--   Definitions and structural lemmas for Statements Proj Max Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsProjMaxRank.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjFullRankDense
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
def projMaxRank {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {n : ℕ} (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {V : Set R.X} (BV : FinHolAtlas n V) : Set V :=
  {x | ∃ i : Fin (n + 1), Ψ (segre (R.lift x.1 x.1)) i ≠ 0 ∧ ∃ j, x ∈ (BV.chart j).source ∧
    Module.finrank ℂ (LinearMap.range (fderiv ℂ
      (fun u l => Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) l /
        Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) i) (BV.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))) = n}
end GroundTheory.Heights₂.Heights.Targets


