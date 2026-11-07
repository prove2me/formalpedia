-- Prove2me | Definitions.Def_AaronsonAmbainis_RowDefs
-- name    : AaronsonAmbainis_RowDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:34:15.567247+00:00
-- url     : https://prove2.me/theorems/9ca5dc3a-69ca-4c62-9703-e9fcaabcb4dc
-- title:
--   Row Defs
-- statement:
--   Definitions and structural lemmas for Row Defs, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/RowDefs.lean

import Definitions.Def_AaronsonAmbainis_Statements
set_option autoImplicit true
namespace AaronsonAmbainis
open Finset
def MarkovEndpoint : Prop :=
  ∀ (D : ℕ) (p : Polynomial ℝ), p.natDegree ≤ D →
    (∀ s : ℝ, 0 ≤ s → s ≤ 2 → |p.eval s| ≤ 1) → |p.derivative.eval 0| ≤ (D : ℝ) ^ 2
def BlockInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d →
  ∀ (x : Cube ι) (β : Type) [Fintype β] (S : β → Finset ι) (N m : ℕ), 0 < m →
    (∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) →
    (N : ℝ) * (1 - Real.cos (Real.pi / (m : ℝ))) ≤ 2 →
    ∑ b, |f x - f (flipSet x (S b))| ≤ 4 * (d : ℝ) ^ 2 * (m : ℝ) ^ 2
def PackingBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d →
  ∀ (x : Cube ι) (κ : Finset ι → ℝ), (∀ S, 0 ≤ κ S) →
    (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
    ∑ S, κ S * |f x - f (flipSet x S)| ≤ Real.pi ^ 2 * (d : ℝ) ^ 2
def CoverDuality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (t : Finset ι → ℝ) (K : ℝ), 0 ≤ K → t ∅ ≤ 0 →
    (∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K) →
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ K ∧ ∀ S : Finset ι, t S ≤ ∑ i ∈ S, a i
def RowBoundPM : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d →
    ∃ a : Cube ι → ι → ℝ, (∀ x i, 0 ≤ a x i) ∧
      (∀ x, ∑ i, a x i ≤ Real.pi ^ 2 * (d : ℝ) ^ 2) ∧
      ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i
end AaronsonAmbainis


