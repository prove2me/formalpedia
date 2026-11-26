-- Prove2me | Definitions.Def_EconomicsNextProof_Basic
-- name    : EconomicsNextProof_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:12:43.472904+00:00
-- url     : https://prove2.me/theorems/a09275d2-b628-4644-a7dc-6b3bac791f9c
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/falmagne-block-marschak-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Falmagne-Block-Marschak random-utility characterization of stochastic choice rules development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Basic.lean

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
def IsRanking (l : List X) : Prop :=
  l.Nodup ∧ l.toFinset = Finset.univ
def lowerContour (l : List X) (x : X) : Finset X :=
  l.toFinset.filter fun y => l.idxOf x ≤ l.idxOf y
noncomputable def rankingChoice (l : List X) (A : Finset X) (x : X) : ℝ :=
  if x ∈ A ∧ A ⊆ lowerContour l x then 1 else 0
abbrev RankingLaw (X : Type*) := List X →₀ ℝ
def IsRankingLaw (w : RankingLaw X) : Prop :=
  (∀ l, 0 ≤ w l) ∧
  (∀ l ∈ w.support, IsRanking l) ∧
  w.sum (fun _ a => a) = 1
def IsChoiceRule (p : Finset X → X → ℝ) : Prop :=
  (∀ A x, 0 ≤ p A x) ∧
  (∀ A x, x ∉ A → p A x = 0) ∧
  (∀ A, A.Nonempty → ∑ x ∈ A, p A x = 1)
def Represents (w : RankingLaw X) (p : Finset X → X → ℝ) : Prop :=
  ∀ A x, p A x = w.sum (fun l a => a * rankingChoice l A x)
variable {l : List X} {A : Finset X} {x y : X}
end Falmagne


