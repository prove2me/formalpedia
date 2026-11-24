-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSectionLength
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSectionLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:42.143415+00:00
-- url     : https://prove2.me/theorems/b78f3eaa-3622-4982-9363-c90ab9e6b8cd
-- title:
--   St Chart Section Length
-- statement:
--   Definitions and structural lemmas for St Chart Section Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StChartSectionLength.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSection
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal multAt PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartComponents localMult)
def ChartSectionLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      ∀ W, W ∈ divSupp P s → IsHorizontal W → ∀ W' ∈ segreChartComponents W σ i,
        localMult (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}) W' =
          multAt (P ⊔ Ideal.span {s}) W
end GroundTheory.Heights₂.Heights.Targets


