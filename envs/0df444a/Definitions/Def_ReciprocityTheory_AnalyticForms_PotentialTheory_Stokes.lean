-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:27.577096+00:00
-- url     : https://prove2.me/theorems/616a64bc-3ce5-4a0f-867b-df046bcf7635
-- title:
--   Stokes
-- statement:
--   Definitions and structural lemmas for Stokes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Stokes.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
def LocalSymmStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (j : Fin A.n) (χ w : X → ℝ), A.Smooth χ → A.Smooth w →
    tsupport χ ⊆ (A.chart j).source → ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun w) Φ) χ = mInt A (Fin.cons (LocPot.ofFun χ) Φ) w
def MIntConstPotStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X) (c : ℝ)
    (Φ : Fin e → LocPot X) (g : X → ℝ), mInt A (Fin.cons (LocPot.ofFun fun _ => c) Φ) g = 0
end
end ReciprocityTheory.AnForm.M


