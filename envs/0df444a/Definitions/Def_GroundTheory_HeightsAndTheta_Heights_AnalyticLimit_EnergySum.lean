-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_EnergySum
-- name    : GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_EnergySum
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:28:16.248295+00:00
-- url     : https://prove2.me/theorems/46dbaf12-9452-5bd8-8020-df88b3ec3549
-- title:
--   Energy Sum
-- statement:
--   Definitions and structural lemmas for Energy Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/EnergySum.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isPlurisubharmonic
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isSmoothPotential
import Theorems.Thm_ReciprocityTheory_AnForm_M_projectiveLine_fubiniStudy_mass_one
import Theorems.Thm_ReciprocityTheory_AnForm_M_projectiveLine_locDens_first_chart
import Theorems.Thm_ReciprocityTheory_AnForm_M_projectiveLine_locDens_second_chart
import Theorems.Thm_ReciprocityTheory_AnForm_integrable_fsDens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
open MeasureTheory
open scoped ContDiff ComplexOrder
open ReciprocityTheory.AnForm (hessC maDens mdisc levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens integralWith)
noncomputable section
open scoped Classical in

def tvInt {D : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas D X) (Φ : Fin D → LocPot X)
    (g : X → ℝ) : ℝ :=
  if h : Nonempty (ChartPartition A) then
    ∑ j, ∫ y in (A.chart j).target,
      h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * |locDens A Φ j y|
  else 0
def EnergySum.Statement : Prop :=
  ∀ (D : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (m : ℕ)
    (P : Fin m → LocPot X) (a : Fin D → Fin m → ℝ) (V : ℝ),
    (∀ i, IsPotential A (P i)) → (∀ i, FormNonneg A Yo (P i)) →
    (∀ σ : Fin D → Fin m,
      (∀ (Q : ChartPartition A) (j : Fin A.n), IntegrableOn (fun y =>
          Q.χ j ((A.chart j).symm y) * Yo.indicator 1 ((A.chart j).symm y) *
            locDens A (fun k => P (σ k)) j y) (A.chart j).target) ∧
      mInt A (fun k => P (σ k)) (Yo.indicator 1) ≤ V) →
    tvInt A (fun k => lincomb m (a k) P) (Yo.indicator 1) ≤ (∏ k, ∑ i, |a k i|) * V
section Proof
variable {D : ℕ}
variable {X : Type*} [TopologicalSpace X]
end Proof
section Inhabitant
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic projectiveLine_fubiniStudy_mass_one p1i0 p1i1 projectiveLine_locDens_first_chart projectiveLine_locDens_second_chart)
open ReciprocityTheory.AnForm (fsDens integrable_fsDens)
end Inhabitant
end
end GroundTheory.Heights₂.Heights.AnalyticLimit


