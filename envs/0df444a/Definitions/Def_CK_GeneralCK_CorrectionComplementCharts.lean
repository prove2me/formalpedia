-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionComplementCharts
-- name    : CK_GeneralCK_CorrectionComplementCharts
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:59:58.499987+00:00
-- url     : https://prove2.me/theorems/3bf98f58-9a94-4d2b-b176-a6380afb641e
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionComplementCharts` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionComplementCharts` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionComplementCharts` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionComplementCharts (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionComplementCharts.lean)

import Definitions.Def_CK_GeneralCK_CorrectionComplementLedger

/-!
# Explicit chart coverage for correction

This is the exact rational coverage architecture from manuscript Q.3,
with the two high-ratio corner strips also removed from C5 and C6.
All analytic chart signs remain explicit premises. No numerical ledger
or isolated local certificate is treated as a completed family.
-/

namespace GeneralCK.Correction.Complement
open Set

def SignsOnBox (u0 u1 r0 r1 : ℝ) : Prop :=
  ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    u ∈ Icc u0 u1 → rho ∈ Icc r0 r1 → RatioSigns u rho

structure ChartOwners : Prop where
  bothSmall : ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    u + rho * (1 / 2 - u) ≤ 1 / 40 → RatioSigns u rho
  fixedEdge : ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    u ≤ 1 / 50 → 1 / 40 ≤ u + rho * (1 / 2 - u) → RatioSigns u rho
  diagonal1 : SignsOnBox (1/50) (1/10) 0 (3/40)
  diagonal2 : SignsOnBox (1/10) (1/5) 0 (1/10)
  diagonal3 : SignsOnBox (1/5) (3/10) 0 (3/20)
  diagonal4 : SignsOnBox (3/10) (9/25) 0 (11/50)
  diagonal5 : SignsOnBox (9/25) (37/100) 0 (1/10)
  diagonal6 : SignsOnBox (37/100) (19/50) 0 (3/10)
  diagonal7 : SignsOnBox (19/50) (39/100) 0 (2/5)
  diagonal8 : SignsOnBox (39/100) (2/5) 0 (1/5)
  diagonal9 : SignsOnBox (2/5) (41/100) 0 (1/20)
  directC3 : SignsOnBox (1/5) (3/10) (3/20) 1
  directC4 : SignsOnBox (3/10) (9/25) (11/50) 1
  directC5 : SignsOnBox (9/25) (37/100) (1/10) (9/10)
  directC6 : SignsOnBox (37/100) (19/50) (3/10) (7/10)
  corner0 : SignsOnBox (41/100) (1/2) (0) 1
  corner1 : SignsOnBox (2/5) (1/2) (1/20) 1
  corner2 : SignsOnBox (39/100) (1/2) (1/5) 1
  corner3 : SignsOnBox (19/50) (1/2) (2/5) 1
  corner4 : SignsOnBox (37/100) (1/2) (7/10) 1
  corner5 : SignsOnBox (9/25) (1/2) (9/10) 1

theorem full_ratio_signs_of_charts
    (hC1 : ActualRatioFamilyOn (1/50) (1/10) (3/40) 1)
    (hC2 : ActualRatioFamilyOn (1/10) (1/5) (1/10) 1)
    (h : ChartOwners) :
    ∀ u rho : ℝ, 0 < u → u < 1/2 → 0 < rho → rho < 1 →
      RatioSigns u rho := by
  intro u rho hu hu' hr hr'
  by_cases hu50 : u ≤ 1/50
  · by_cases hw40 : u + rho * (1/2-u) ≤ 1/40
    · exact h.bothSmall hu hu' hr hr' hw40
    · exact h.fixedEdge hu hu' hr hr' hu50 (le_of_lt (lt_of_not_ge hw40))
  have lower0 : (1/50 : ℝ) ≤ u := (lt_of_not_ge hu50).le
  by_cases upper1 : u ≤ (1/10 : ℝ)
  · by_cases ratio1 : rho ≤ (3/40 : ℝ)
    · exact h.diagonal1 hu hu' hr hr' ⟨lower0, upper1⟩ ⟨hr.le, ratio1⟩
    · exact ratioSigns_of_positive (hC1 ⟨lower0, upper1⟩ ⟨(le_of_lt (lt_of_not_ge ratio1)), hr'.le⟩ hr')
  have lower1 : (1/10 : ℝ) ≤ u := (lt_of_not_ge upper1).le
  by_cases upper2 : u ≤ (1/5 : ℝ)
  · by_cases ratio2 : rho ≤ (1/10 : ℝ)
    · exact h.diagonal2 hu hu' hr hr' ⟨lower1, upper2⟩ ⟨hr.le, ratio2⟩
    · exact ratioSigns_of_positive (hC2 ⟨lower1, upper2⟩ ⟨(le_of_lt (lt_of_not_ge ratio2)), hr'.le⟩ hr')
  have lower2 : (1/5 : ℝ) ≤ u := (lt_of_not_ge upper2).le
  by_cases upper3 : u ≤ (3/10 : ℝ)
  · by_cases ratio3 : rho ≤ (3/20 : ℝ)
    · exact h.diagonal3 hu hu' hr hr' ⟨lower2, upper3⟩ ⟨hr.le, ratio3⟩
    · exact h.directC3 hu hu' hr hr' ⟨lower2, upper3⟩ ⟨(le_of_lt (lt_of_not_ge ratio3)), hr'.le⟩
  have lower3 : (3/10 : ℝ) ≤ u := (lt_of_not_ge upper3).le
  by_cases upper4 : u ≤ (9/25 : ℝ)
  · by_cases ratio4 : rho ≤ (11/50 : ℝ)
    · exact h.diagonal4 hu hu' hr hr' ⟨lower3, upper4⟩ ⟨hr.le, ratio4⟩
    · exact h.directC4 hu hu' hr hr' ⟨lower3, upper4⟩ ⟨(le_of_lt (lt_of_not_ge ratio4)), hr'.le⟩
  have lower4 : (9/25 : ℝ) ≤ u := (lt_of_not_ge upper4).le
  by_cases upper5 : u ≤ (37/100 : ℝ)
  · by_cases ratio5 : rho ≤ (1/10 : ℝ)
    · exact h.diagonal5 hu hu' hr hr' ⟨lower4, upper5⟩ ⟨hr.le, ratio5⟩
    · by_cases top5 : rho ≤ (9/10 : ℝ)
      · exact h.directC5 hu hu' hr hr' ⟨lower4, upper5⟩ ⟨(le_of_lt (lt_of_not_ge ratio5)), top5⟩
      · exact h.corner5 hu hu' hr hr' ⟨lower4, hu'.le⟩ ⟨(lt_of_not_ge top5).le, hr'.le⟩
  have lower5 : (37/100 : ℝ) ≤ u := (lt_of_not_ge upper5).le
  by_cases upper6 : u ≤ (19/50 : ℝ)
  · by_cases ratio6 : rho ≤ (3/10 : ℝ)
    · exact h.diagonal6 hu hu' hr hr' ⟨lower5, upper6⟩ ⟨hr.le, ratio6⟩
    · by_cases top6 : rho ≤ (7/10 : ℝ)
      · exact h.directC6 hu hu' hr hr' ⟨lower5, upper6⟩ ⟨(le_of_lt (lt_of_not_ge ratio6)), top6⟩
      · exact h.corner4 hu hu' hr hr' ⟨lower5, hu'.le⟩ ⟨(lt_of_not_ge top6).le, hr'.le⟩
  have lower6 : (19/50 : ℝ) ≤ u := (lt_of_not_ge upper6).le
  by_cases upper7 : u ≤ (39/100 : ℝ)
  · by_cases ratio7 : rho ≤ (2/5 : ℝ)
    · exact h.diagonal7 hu hu' hr hr' ⟨lower6, upper7⟩ ⟨hr.le, ratio7⟩
    · exact h.corner3 hu hu' hr hr' ⟨lower6, hu'.le⟩ ⟨(le_of_lt (lt_of_not_ge ratio7)), hr'.le⟩
  have lower7 : (39/100 : ℝ) ≤ u := (lt_of_not_ge upper7).le
  by_cases upper8 : u ≤ (2/5 : ℝ)
  · by_cases ratio8 : rho ≤ (1/5 : ℝ)
    · exact h.diagonal8 hu hu' hr hr' ⟨lower7, upper8⟩ ⟨hr.le, ratio8⟩
    · exact h.corner2 hu hu' hr hr' ⟨lower7, hu'.le⟩ ⟨(le_of_lt (lt_of_not_ge ratio8)), hr'.le⟩
  have lower8 : (2/5 : ℝ) ≤ u := (lt_of_not_ge upper8).le
  by_cases upper9 : u ≤ (41/100 : ℝ)
  · by_cases ratio9 : rho ≤ (1/20 : ℝ)
    · exact h.diagonal9 hu hu' hr hr' ⟨lower8, upper9⟩ ⟨hr.le, ratio9⟩
    · exact h.corner1 hu hu' hr hr' ⟨lower8, hu'.le⟩ ⟨(le_of_lt (lt_of_not_ge ratio9)), hr'.le⟩
  have lower9 : (41/100 : ℝ) ≤ u := (lt_of_not_ge upper9).le
  exact h.corner0 hu hu' hr hr' ⟨lower9, hu'.le⟩ ⟨hr.le, hr'.le⟩

theorem remainingOwners_of_charts
    (hC1 : ActualRatioFamilyOn (1/50) (1/10) (3/40) 1)
    (hC2 : ActualRatioFamilyOn (1/10) (1/5) (1/10) 1)
    (h : ChartOwners) : RemainingOwners := by
  have hf := full_ratio_signs_of_charts hC1 hC2 h
  exact ⟨fun _ _ hu hu' hr hr' _ => hf _ _ hu hu' hr hr',
    fun _ _ hu hu' hr hr' _ => hf _ _ hu hu' hr hr',
    fun _ _ hu hu' hr hr' _ => hf _ _ hu hu' hr hr',
    fun _ _ hu hu' hr hr' _ => hf _ _ hu hu' hr hr'⟩

theorem orderedTriangle_signs_of_charts
    (hC1 : ActualRatioFamilyOn (1/50) (1/10) (3/40) 1)
    (hC2 : ActualRatioFamilyOn (1/10) (1/5) (1/10) 1)
    (h : ChartOwners) :
    (∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2) ∧
    (∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2) :=
  orderedTriangle_signs_of_owners hC1 hC2 (remainingOwners_of_charts hC1 hC2 h)

#print axioms full_ratio_signs_of_charts
#print axioms orderedTriangle_signs_of_charts
end GeneralCK.Correction.Complement


