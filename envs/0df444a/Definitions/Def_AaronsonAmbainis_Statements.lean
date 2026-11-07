-- Prove2me | Definitions.Def_AaronsonAmbainis_Statements
-- name    : AaronsonAmbainis_Statements
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:16:32.566721+00:00
-- url     : https://prove2.me/theorems/a1fe10e2-f8cc-4ba9-b0a1-3e0b44a2c81a
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Statements.lean

import Definitions.Def_AaronsonAmbainis_Defs
set_option autoImplicit true
namespace AaronsonAmbainis
open Finset
def DetInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (ℓ : ι → ℝ), (∀ j, 0 < ℓ j) →
  ∀ (A : Cube ι → Finset ι), (∀ u ∈ zone g, IsWing g u (A u)) →
  ∀ (d : Cube ι → ℝ),
    (∀ u ∈ zone g, ∀ G : Finset ι, Disjoint G (A u) →
        g (flipSet (antipode u) G) = true → d u ≤ ∑ j ∈ G, ℓ j) →
    ∑ u ∈ zone g, d u ≤ ∑ j, ℓ j * (bdry g j : ℝ)
def AntipodalInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (w : ι → ℝ), (∀ j, 0 < w j) →
  ∀ (lam : Cube ι → ι → ℝ), (∀ x, IsRow g x (lam x)) →
    ∑ u ∈ zone g, (∑ j, w j * lam u j * lam (antipode u) j)⁻¹ ≤ ∑ j, (bdry g j : ℝ) / w j
def TwoSidedInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (lam : Cube ι → ι → ℝ), (∀ x, IsRow g x (lam x)) →
  ∀ τ : ℝ, 0 ≤ τ → (∀ j, infl g j ≤ τ) →
    4 * ((∑ x ∈ univ.filter (fun x : Cube ι => g x = true), (∑ j, lam x j)⁻¹) / 2 ^ Fintype.card ι)
      * ((∑ x ∈ univ.filter (fun x : Cube ι => g x = false), (∑ j, lam x j)⁻¹) / 2 ^ Fintype.card ι) ≤ τ
def IntegratedAllPairsInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ),
    (∀ x j, 0 ≤ a x j) → (∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) →
  ∀ (w : ι → ℝ), (∀ j, 0 < w j) →
    ∑ x, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      ≤ 4 ^ (Fintype.card ι - 1) * ∑ j, meanAbsIncr f j / w j
def ThirdMomentInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (K : ℝ) (a : Cube ι → ι → ℝ),
    (∀ x j, 0 ≤ a x j) → (∀ x, ∑ j, a x j ≤ K) →
    (∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) →
  ∀ (M : ℝ), 0 ≤ M → (∀ j, meanAbsIncr f j ≤ M) → ∀ r : ℝ,
    (∑ x, max (f x - r) 0 ^ 3) / 2 ^ Fintype.card ι
        * (((univ.filter (fun y : Cube ι => f y ≤ r)).card : ℝ) / 2 ^ Fintype.card ι)
      ≤ 3 / 2 * K ^ 2 * M
def MeanIncrementBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (K : ℝ) (a : Cube ι → ι → ℝ),
    (∀ x j, 0 ≤ a x j) → (∀ x, ∑ j, a x j ≤ K) →
    (∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) → 0 < variance f →
    ∃ j, variance f ^ 3 ≤ 36 * K ^ 4 * meanAbsIncr f j ^ 2
def InfluenceBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (K : ℝ) (a : Cube ι → ι → ℝ),
    (∀ x j, 0 ≤ a x j) → (∀ x, ∑ j, a x j ≤ K) →
    (∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) → 0 < variance f →
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * (∑ k, meanAbsIncr f k) ^ 2 * K ^ 4 * inflR f j ^ 2
def SensitivityBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → ∀ x : Cube ι, ∑ j, |f x - f (flipSet x {j})| ≤ 4 * (d : ℝ) ^ 2
def MainTheorem : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    ∃ j, 3 * variance f ^ 5 ≤ 50000 * Real.pi ^ 8 * (d : ℝ) ^ 12 * inflR f j ^ 2
def MeanIncrementDegreeBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    ∃ j, variance f ^ 3 ≤ 36 * Real.pi ^ 8 * (d : ℝ) ^ 8 * meanAbsIncr f j ^ 2
def RowBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) → HasDegreeLE f d →
    ∃ c : Cube ι → ι → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2)
def MainTheoremImproved : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12 * inflR f j ^ 2
end AaronsonAmbainis


