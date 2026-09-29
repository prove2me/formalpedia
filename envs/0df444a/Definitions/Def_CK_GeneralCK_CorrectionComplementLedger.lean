-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionComplementLedger
-- name    : CK_GeneralCK_CorrectionComplementLedger
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:48:36.115987+00:00
-- url     : https://prove2.me/theorems/1744ba8b-9769-4724-b581-cd60a75691f2
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionComplementLedger` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionComplementLedger` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionComplementLedger` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionComplementLedger (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionComplementLedger.lean)

import Definitions.Def_CK_GeneralCK_CorrectionCertifiedBandClosure

/-!
# Exact correction-complement ledger

This module proves geometric coverage and conditional assembly only.
It does not assert that the four remaining analytic owners are inhabited.
The determinant conclusion is non-strict, as required by the original task.
-/

namespace GeneralCK.Correction.Complement
open Set

def LowU (u rho : ℝ) : Prop := u < 1 / 50
def HighU (u rho : ℝ) : Prop := 1 / 5 < u
def LowRatioC1 (u rho : ℝ) : Prop :=
  1 / 50 ≤ u ∧ u ≤ 1 / 10 ∧ rho < 3 / 40
def LowRatioC2 (u rho : ℝ) : Prop :=
  1 / 10 < u ∧ u ≤ 1 / 5 ∧ rho < 1 / 10

def ExactRemainder (u rho : ℝ) : Prop :=
  LowU u rho ∨ HighU u rho ∨ LowRatioC1 u rho ∨ LowRatioC2 u rho

theorem exactRemainder_iff (u rho : ℝ) :
    ExactRemainder u rho ↔ OutsideCertifiedC1C2Region u rho := by
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨h.2.1, h.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.1, h.2.2⟩))
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · by_cases hu : u < 1 / 50
      · exact Or.inl hu
      · exact Or.inr (Or.inr (Or.inl ⟨le_of_not_gt hu, h.1, h.2⟩))
    · by_cases hu : 1 / 5 < u
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr (Or.inr ⟨h.1, le_of_not_gt hu, h.2⟩))

/-- All four pieces are disjoint, including their rational threshold faces. -/
theorem pieces_disjoint {u rho : ℝ} :
    (LowU u rho → ¬ HighU u rho ∧ ¬ LowRatioC1 u rho ∧ ¬ LowRatioC2 u rho) ∧
    (HighU u rho → ¬ LowRatioC1 u rho ∧ ¬ LowRatioC2 u rho) ∧
    (LowRatioC1 u rho → ¬ LowRatioC2 u rho) := by
  dsimp [LowU, HighU, LowRatioC1, LowRatioC2]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro h'; linarith
    · rintro ⟨h', _⟩; linarith
    · rintro ⟨h', _⟩; linarith
  constructor
  · intro h
    constructor
    · rintro ⟨_, h', _⟩; linarith
    · rintro ⟨_, h', _⟩; linarith
  · rintro ⟨_, h, _⟩ ⟨h', _⟩
    linarith

/-- The exact sign strength requested by the task, in probability coordinates. -/
def RatioSigns (u rho : ℝ) : Prop :=
  0 < Mleft (H u) (H (u + rho * (1 / 2 - u))) ∧
  0 ≤ Mdet (H u) (H (u + rho * (1 / 2 - u)))

theorem ratioSigns_of_positive {u rho : ℝ}
    (h : ActualRatioMinorsPositive u rho) : RatioSigns u rho :=
  ⟨h.1, h.2.le⟩

/-- Separate analytic obligations for all four exact complement pieces. -/
structure RemainingOwners : Prop where
  lowU : ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    LowU u rho → RatioSigns u rho
  highU : ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    HighU u rho → RatioSigns u rho
  lowRatioC1 : ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    LowRatioC1 u rho → RatioSigns u rho
  lowRatioC2 : ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    LowRatioC2 u rho → RatioSigns u rho

theorem RemainingOwners.outside (h : RemainingOwners) {u rho : ℝ}
    (hu : 0 < u) (hu' : u < 1 / 2) (hr : 0 < rho) (hr' : rho < 1)
    (hout : OutsideCertifiedC1C2Region u rho) : RatioSigns u rho := by
  rcases (exactRemainder_iff u rho).mpr hout with h0 | h1 | h2 | h3
  · exact h.lowU hu hu' hr hr' h0
  · exact h.highU hu hu' hr hr' h1
  · exact h.lowRatioC1 hu hu' hr hr' h2
  · exact h.lowRatioC2 hu hu' hr hr' h3

theorem full_ratio_signs_of_owners
    (hC1 : ActualRatioFamilyOn (1 / 50) (1 / 10) (3 / 40) 1)
    (hC2 : ActualRatioFamilyOn (1 / 10) (1 / 5) (1 / 10) 1)
    (h : RemainingOwners) :
    ∀ u rho : ℝ, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
      RatioSigns u rho := by
  intro u rho hu hu' hr hr'
  by_cases hu10 : u ≤ 1 / 10
  · by_cases hu50 : 1 / 50 ≤ u
    · by_cases hr40 : 3 / 40 ≤ rho
      · exact ratioSigns_of_positive (hC1 ⟨hu50, hu10⟩ ⟨hr40, hr'.le⟩ hr')
      · exact h.lowRatioC1 hu hu' hr hr' ⟨hu50, hu10, lt_of_not_ge hr40⟩
    · exact h.lowU hu hu' hr hr' (lt_of_not_ge hu50)
  · have hu10' : 1 / 10 < u := lt_of_not_ge hu10
    by_cases hu5 : u ≤ 1 / 5
    · by_cases hr10 : 1 / 10 ≤ rho
      · exact ratioSigns_of_positive (hC2 ⟨hu10'.le, hu5⟩ ⟨hr10, hr'.le⟩ hr')
      · exact h.lowRatioC2 hu hu' hr hr' ⟨hu10', hu5, lt_of_not_ge hr10⟩
    · exact h.highU hu hu' hr hr' (lt_of_not_ge hu5)

/-- The global target follows from the two accepted families and all four
remaining owners. None of those analytic premises is silently discharged. -/
theorem orderedTriangle_signs_of_owners
    (hC1 : ActualRatioFamilyOn (1 / 50) (1 / 10) (3 / 40) 1)
    (hC2 : ActualRatioFamilyOn (1 / 10) (1 / 5) (1 / 10) 1)
    (h : RemainingOwners) :
    (∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2) ∧
    (∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2) := by
  have hfam := full_ratio_signs_of_owners hC1 hC2 h
  have hpoint : ∀ e f : ℝ, (e, f) ∈ orderedTriangle →
      0 < Mleft e f ∧ 0 ≤ Mdet e f := by
    intro e f htri
    have hc := orderedTriangle_probability_ratio htri
    dsimp only at hc
    rcases hc with ⟨hu, hu', hr, hr', hw, hHu, hHw⟩
    have hs := hfam (entropyInverse e)
      ((entropyInverse f - entropyInverse e) / (1 / 2 - entropyInverse e))
      hu hu' hr hr'
    unfold RatioSigns at hs
    rw [hw, hHu, hHw] at hs
    exact hs
  constructor
  · rintro ⟨e, f⟩ hp
    exact (hpoint e f hp).1
  · rintro ⟨e, f⟩ hp
    exact (hpoint e f hp).2

/-- A concrete geometric witness that the certified C1/C2 union is incomplete. -/
theorem low_u_is_uncovered :
    OutsideCertifiedC1C2Region (1 / 100 : ℝ) (1 / 2) := by
  exact Or.inl (by norm_num)

#print axioms exactRemainder_iff
#print axioms pieces_disjoint
#print axioms orderedTriangle_signs_of_owners
end GeneralCK.Correction.Complement


