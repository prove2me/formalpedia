-- Prove2me | Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
-- name    : AaronsonAmbainis_Bridge_PaperTheorems
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:12:58.753991+00:00
-- url     : https://prove2.me/theorems/8d35daee-0540-4fef-a9e6-2bd2f8f6e834
-- title:
--   Paper Theorems
-- statement:
--   Definitions and structural lemmas for Paper Theorems, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperTheorems.lean

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
namespace AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def RowBoundPMPrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d →
    ∀ x : Cube ι, ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 ∧
      ∀ S : Finset ι, |f x - f (flipSet x S)| ≤ ∑ i ∈ S, a i
def MeanIncrementPrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (K : ℝ),
    (∀ x : Cube ι, ∃ a : ι → ℝ, (∀ j, 0 ≤ a j) ∧ ∑ j, a j ≤ K ∧
      ∀ S : Finset ι, |f x - f (flipSet x S)| ≤ ∑ j ∈ S, a j) →
    0 < variance f →
    0 < K ∧ ∃ j, variance f ^ 3 ≤ 36 * K ^ 4 * meanAbsIncr f j ^ 2 ∧
      variance f * Real.sqrt (variance f) / (6 * K ^ 2) ≤ meanAbsIncr f j
def InfluencePrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (K : ℝ),
    (∀ x : Cube ι, ∃ a : ι → ℝ, (∀ j, 0 ≤ a j) ∧ ∑ j, a j ≤ K ∧
      ∀ S : Finset ι, |f x - f (flipSet x S)| ≤ ∑ j ∈ S, a j) →
    0 < variance f →
    0 < ∑ k, meanAbsIncr f k ∧ ∑ k, meanAbsIncr f k ≤ K ∧
      ∃ j, 3 * variance f ^ 5 ≤ 3125 * (∑ k, meanAbsIncr f k) ^ 2 * K ^ 4 * inflR f j ^ 2 ∧
        Real.sqrt 15 / 125 * (variance f ^ 2 * Real.sqrt (variance f))
            / ((∑ k, meanAbsIncr f k) * K ^ 2) ≤ inflR f j ∧
        Real.sqrt 15 / 125 * (variance f ^ 2 * Real.sqrt (variance f)) / K ^ 3 ≤ inflR f j
def MeanIncrementDegreePrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    1 ≤ d ∧ ∃ j, variance f * Real.sqrt (variance f) / (6 * Real.pi ^ 4 * (d : ℝ) ^ 4)
      ≤ meanAbsIncr f j
def MainTheoremPrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (d : ℕ), 1 ≤ d →
    ∀ f : Cube ι → ℝ, (∀ x, |f x| ≤ 1) → HasDegreeLE f d →
    ∃ j, Real.sqrt 15 / (500 * Real.pi ^ 4) * (variance f ^ 2 * Real.sqrt (variance f))
      / (d : ℝ) ^ 6 ≤ inflR f j
end AaronsonAmbainis.Bridge


