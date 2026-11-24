-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_MUConjInv
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_MUConjInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:53.394388+00:00
-- url     : https://prove2.me/theorems/8665492d-6f12-4b02-a388-483a91672a9c
-- title:
--   MUConj Inv
-- statement:
--   Definitions and structural lemmas for MUConj Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/MUConjInv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FlagSectionNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_Imports
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace ComponentData
variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
def MUConjInv (D : ComponentData Ψ K ι) : Prop :=
  ∀ B : ℕ, 4 * D.f + 2 ≤ B → ∀ eps t' : ℝ, 0 < eps → eps ≤ 1 → 0 < t' → t' ≤ 1 → (D.MU B eps t').IsConjInv
end ComponentData
open ComponentData
def LowerBoundComponentConjugate.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (D : ComponentData Ψ K ι) (II : IntersectionSystem) (Ch Cu : ℝ) (B : ℕ),
    D.Clauses → IsIntersectionSystem II → D.KBound II →
    ZhangLowerX.Statement → DimX.Statement → D.CuspBundlePos → D.MUConjInv → D.HtInterior II Ch →
    D.HtBoundary II Ch → StokesLimit.Statement → D.CuspMean Cu → PushDown.Statement → GrassmannianHeightZTwo.Statement →
    1 ≤ D.jp → 3 * D.jp + 1 ≤ D.N → 4 * D.f * D.N ^ 2 ≤ B → 4 * D.f + 2 ≤ B →
    ∀ vol : ℝ, ((cf D.n : ℚ) : ℝ) * (D.fdeg' : ℝ) * D.degMu = vol * (D.J' : ℝ) →
      -(Ch + Cu / 2) * D.f * D.jp * D.abelian₂ B ≤ D.PPB II B / (((D.n + 1 : ℕ) : ℝ) * vol * (D.J' : ℝ))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine


