-- Prove2me | Definitions.Def_ChoresTIE197_Main_TwoAgent
-- name    : ChoresTIE197_Main_TwoAgent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T02:17:07.621949+00:00
-- url     : https://prove2.me/theorems/a17d92f4-57a7-4645-b3fe-d6117f6c6801
-- title:
--   The two-cost balancing routines and Mechanism 3
-- statement:
--   For two cost rows on a finite chore set, the balancing routine contracts a comparable pair into their cost difference, recursively balances the reduced list, and expands the two original chores onto opposite sides. If no comparable pair exists, it alternates chores sorted by the first row. Empty input returns empty parts.
--
--   For a shared top nomination, the common partition routine uses the three cases in Lemma B.2: both top costs small, both large, or a mixed case with three threshold-greedy sets and a least-cost choice. With distinct nominations it balances the residual chores as in Lemma B.3. These are operational constructions; their result types do not contain any asserted MMS bound.
--
--   Mechanism 3 draws one fair coin. Shared nominations cause a random swap of the complementary parts. Distinct nominations are sent to the opposite agents, while only the two residual parts are randomly swapped. Thus every outcome is one complete allocation.
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Appendix B, Lemmas B.1–B.3 and Mechanism 3, printed p.35, PDF p.35; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Setting
import Definitions.Def_ChoresTIE197_Main_Rounding

open Finset
open Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

abbrev WorkChore := ℕ × ℝ × ℝ

def workCost (i : Fin 2) (e : WorkChore) : ℝ := if i = 0 then e.2.1 else e.2.2

/-- B.1: contract a comparable pair, recurse, expand on opposite sides.
Without a comparable pair, alternate along the first cost's descending order. -/
def balanceWork : ℕ → List WorkChore → (ℕ → Bool)
  | 0, _ => fun _ => false
  | fuel + 1, S =>
    let pairs := (S.flatMap (fun a => S.map (fun b => (a,b)))).filter (fun z =>
      z.1.1 ≠ z.2.1 ∧ z.2.2.1 ≤ z.1.2.1 ∧ z.2.2.2 ≤ z.1.2.2)
    match pairs.head? with
    | some (a,b) =>
      let T := (S.filter (fun e => e.1 ≠ b.1)).map (fun e =>
        if e.1 = a.1 then (e.1, e.2.1 - b.2.1, e.2.2 - b.2.2) else e)
      let f := balanceWork fuel T
      fun j => if j = b.1 then !(f a.1) else f j
    | none =>
      let T := S.mergeSort (fun a b => b.2.1 ≤ a.2.1)
      fun j => ((T.map (fun e => e.1)).idxOf j) % 2 == 0

def balance {m : ℕ} (c : Profile 2 m) (S : Finset (Fin m)) : Finset (Fin m) :=
  let T := (S.sort (· ≤ ·)).map (fun e => (e.val, (c 0 e : ℝ), (c 1 e : ℝ)))
  S.filter (fun e => balanceWork (S.card + 1) T e.val)

/-- Greedy prefix, stopping at the threshold; no existence hypothesis is supplied. -/
def greedy {m : ℕ} (c : Fin m → ℝ≥0) (τ : ℝ) : List (Fin m) → Finset (Fin m)
  | [] => ∅
  | e :: T => if τ ≤ 0 then ∅ else insert e (greedy c (τ - c e) T)

def nominee {m : ℕ} [NeZero m] (c : Fin m → ℝ≥0) : Fin m :=
  firstBy univ (rank c) 0

def commonPartition {m : ℕ} [NeZero m] (c : Profile 2 m) : Finset (Fin m) :=
  let e := nominee (c 0)
  if (∀ i, (c i e : ℝ) ≤ cost (c i) univ / 3) then
    let A := balance c univ
    (if e ∈ A then A else univ \ A) \ {e}
  else if (∀ i, cost (c i) univ / 3 ≤ (c i e : ℝ)) then ∅
  else
    let large : Fin 2 := if cost (c 0) univ / 3 < (c 0 e : ℝ) then 0 else 1
    let small : Fin 2 := if large = 0 then 1 else 0
    let τ := cost (c small) univ / 3 - c small e
    let R := univ \ {e}
    let S₁ := greedy (c small) τ (R.sort (· ≤ ·))
    let S₂ := greedy (c small) τ ((R \ S₁).sort (· ≤ ·))
    let S₃ := greedy (c small) τ ((R \ (S₁ ∪ S₂)).sort (· ≤ ·))
    if cost (c large) S₁ ≤ cost (c large) S₂ ∧ cost (c large) S₁ ≤ cost (c large) S₃ then S₁
    else if cost (c large) S₂ ≤ cost (c large) S₃ then S₂ else S₃

def distinctPartition {m : ℕ} [NeZero m] (c : Profile 2 m) : Finset (Fin m) :=
  balance c (univ \ {nominee (c 0), nominee (c 1)})

/-- Mechanism 3, including the common-nomination branch and the swapped nominees. -/
def mechanism3 {m : ℕ} [NeZero m] : Mechanism 2 m := fun c =>
  let e₀ := nominee (c 0)
  let e₁ := nominee (c 1)
  let P := if e₀ = e₁ then commonPartition c else distinctPartition c
  (PMF.uniformOfFintype Bool).map (fun flip e =>
    if e₀ = e₁ then
      if (e ∈ insert e₀ P) = flip then 0 else 1
    else if e = e₀ then 1 else if e = e₁ then 0
    else if (e ∈ P) = flip then 0 else 1)

end ChoresTIE197.Main


