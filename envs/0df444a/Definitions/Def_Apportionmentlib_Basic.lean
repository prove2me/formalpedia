-- Prove2me | Definitions.Def_Apportionmentlib_Basic
-- name    : Apportionmentlib_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:40:31.999801+00:00
-- url     : https://prove2.me/theorems/09385be3-07dc-4a27-8ca7-9644e592184e
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from mdbrnowski/apportionmentlib contributors (see pinned LICENSE and source headers)'s pinned Balinski–Young apportionment impossibility development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mdbrnowski/apportionmentlib/blob/86d9058ae46a2c19c024cdd80e0bb14dbde9b562/Apportionmentlib/Basic.lean

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Rat.Floor
public import Definitions.Def_Apportionmentlib_Utils
public import Theorems.Thm_sum_pos_iff_exists_pos

set_option autoImplicit false
@[expose] public section
@[expose] public section
open BigOperators
namespace Apportionmentlib
structure Election (n : ℕ) where
  /-- The number of votes cast for each of the `n` parties, at the corresponding index. -/
  votes : Vector ℕ n
  /-- The number of seats to be allocated between the parties. -/
  houseSize : ℕ+
  /-- At least one vote is cast, so that the standard quotas are well defined. -/
  votes_sum_pos : 0 < votes.sum
  deriving DecidableEq
instance {n : ℕ} : Repr (Election n) where
  reprPrec e _ :=
    "[" ++ repr e.houseSize ++ "; " ++ repr e.votes.toList ++ "]"
def Election.quota {n : ℕ} (e : Election n) (i : Fin n) : ℚ :=
  (e.votes[i] * e.houseSize : ℚ) / e.votes.sum
@[simp]
def Election.mkByPerm {n : ℕ} (election : Election n) (σ : Equiv.Perm (Fin n)) : Election n :=
  { votes := Vector.ofFn fun i => election.votes[σ i]
    houseSize := election.houseSize
    votes_sum_pos := by
      have := election.votes_sum_pos
      simp only [sum_pos_iff_exists_pos, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta] at this ⊢
      obtain ⟨i, hi⟩ := this
      use σ.symm i
      simpa
  }
@[simp]
def Election.mkByScale {n : ℕ} (election : Election n) (k : ℕ+) : Election n :=
  { votes := Vector.ofFn fun i => k * election.votes[i]
    houseSize := election.houseSize
    votes_sum_pos := by
      have := election.votes_sum_pos
      simpa [sum_pos_iff_exists_pos]
  }
abbrev Apportionment (n : ℕ) : Type := Vector ℕ n
instance {n : ℕ} : Repr (Apportionment n) where
  reprPrec e _ := "#v" ++ repr e.toList
structure Rule where
  /-- The set of apportionments that the rule returns for a given election. -/
  res : {n : ℕ} → Election n → Finset (Apportionment n)
  non_emptiness {n : ℕ} (election : Election n) : (res election).Nonempty
  inheritance_of_zeros {n : ℕ} (election : Election n) (i : Fin n) :
    election.votes[i] = 0 → ∀ App ∈ res election, App[i] = 0
  house_size_feasibility {n : ℕ} (election : Election n) :
    ∀ App ∈ res election, App.sum = election.houseSize
class IsAnonymous (rule : Rule) : Prop where
  anonymous {n : ℕ} (election : Election n) (σ : Equiv.Perm (Fin n)) :
    let election' : Election n := election.mkByPerm σ
    ∀ App, App ∈ rule.res election' ↔
      ∃ App' ∈ rule.res election, ∀ i, App[i] = App'[σ i]
class IsBalanced (rule : Rule) : Prop where
  balanced {n : ℕ} (election : Election n) (i j : Fin n) :
    election.votes[i] = election.votes[j] →
      ∀ App ∈ rule.res election, App[i].dist App[j] ≤ 1
class IsConcordant (rule : Rule) : Prop where
  concordant {n : ℕ} (election : Election n) (i j : Fin n) :
    election.votes[i] < election.votes[j] →
      ∀ App ∈ rule.res election, App[i] ≤ App[j]
class IsDecent (rule : Rule) : Prop where
  decent {n : ℕ} (election : Election n) (k : ℕ+) :
    let election' : Election n := election.mkByScale k
    rule.res election' = rule.res election
class IsExact (rule : Rule) : Prop where
  exact {n : ℕ} (election : Election n) :
    -- ∀ App ∈ rule.res election
    ∀ App : Apportionment n, (hApp : App ∈ rule.res election) →
      let election' : Election n := {
        votes := App
        houseSize := election.houseSize
        votes_sum_pos := by
          rw [rule.house_size_feasibility (n := n) election App hApp]
          exact election.houseSize.pos
      }
      rule.res election' = {App}
class IsQuotaRule (rule : Rule) : Prop where
  quota_rule {n : ℕ} (election : Election n) (i : Fin n) :
    ∀ App ∈ rule.res election, App[i] = ⌊election.quota i⌋ ∨ App[i] = ⌈election.quota i⌉
class IsPopulationMonotone (rule : Rule) : Prop where
  population_monotone {n : ℕ} (election₁ election₂ : Election n) (i j : Fin n) :
    election₁.houseSize = election₂.houseSize →
      -- i's support grows faster than j's (multiplying crosswise to avoid ℚ)
      election₂.votes[i] * election₁.votes[j] > election₂.votes[j] * election₁.votes[i] →
        ∀ App₁ ∈ rule.res election₁, ∀ App₂ ∈ rule.res election₂,
          -- i gets less seats, j gets more seats
          ¬(App₁[i] > App₂[i] ∧ App₁[j] < App₂[j])
section BalinskiYoung
variable (rule : Rule) {a b c : ℕ} {App : Apportionment 4}
def large (a b c : ℕ) : Election 4 :=
  { votes := #v[72, a, b, c], houseSize := 12, votes_sum_pos := by simp }
def small (a b c : ℕ) : Election 4 :=
  { votes := #v[71, a, b, c], houseSize := 12, votes_sum_pos := by simp }
variable [IsQuotaRule rule]
end BalinskiYoung
end Apportionmentlib


