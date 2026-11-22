-- Prove2me | Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
-- name    : LeanPool_CriticalPortraits_Surjectivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:29:37.083002+00:00
-- url     : https://prove2.me/theorems/4bc78619-3e36-406a-9470-427e1dc4ea47
-- title:
--   Surjectivity
-- statement:
--   Definitions and structural lemmas for Surjectivity, from Keston Aquino-Michaels; LeanPool contributors's pinned Counting critical portraits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Theorems.Thm_CriticalPortraits_sameblock_lt

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CriticalPortraits
open Finset
open scoped BigOperators
def Scount {d m : ℕ} (U : Finset (ZMod (d * m))) (x y : ℕ) : ℕ :=
  (U.filter (fun t => x < t.val ∧ t.val < y)).card
def Defc {d m : ℕ} (U : Finset (ZMod (d * m))) (φ lu uval k : ℕ) : ℤ :=
  (Scount U (φ + k*m) uval : ℤ) - ((lu : ℤ) - (k : ℤ) - 1)
open Classical in
/-- The **largest balance index** `K` of survivor `u` (the highest balance parent's level). -/
noncomputable def betaK {d m : ℕ} (U : Finset (ZMod (d * m))) (u : ZMod (d * m)) : ℕ :=
  Nat.findGreatest (fun k => Defc U (u.val % m) (u.val / m) u.val k = 0) (u.val / m - 1)
lemma betaK_le {d m : ℕ} (U : Finset (ZMod (d * m))) (u : ZMod (d * m)) :
    betaK U u ≤ u.val / m - 1 := Nat.findGreatest_le _
noncomputable def betaParentVal {d m : ℕ} (U : Finset (ZMod (d * m))) (u : ZMod (d * m)) : ℕ :=
  u.val % m + betaK U u * m
lemma betaParentVal_lt {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hlu : 1 ≤ u.val / m) :
    betaParentVal U u < d * m := by
  have : NeZero (d*m) := ⟨by positivity⟩
  unfold betaParentVal
  have hφ : u.val % m < m := Nat.mod_lt _ hm
  have hlud : u.val / m < d := by
    have hlt : u.val < d * m := ZMod.val_lt u
    have hdiv : (u.val / m) * m ≤ u.val := Nat.div_mul_le_self u.val m
    by_contra hge
    push Not at hge
    have : d * m ≤ (u.val / m) * m := Nat.mul_le_mul_right m hge
    omega
  have hK : betaK U u ≤ u.val / m - 1 := betaK_le U u
  -- betaK ≤ d - 2, so φ + betaK*m < m + (d-1)*m = d*m
  have hKd : betaK U u ≤ d - 1 := by omega
  have hmul : betaK U u * m ≤ (d-1) * m := Nat.mul_le_mul_right m hKd
  have hdm : (d-1) * m + m = d * m := by
    have : (d - 1) * m + 1 * m = (d - 1 + 1) * m := by rw [← Nat.add_mul]
    rw [Nat.one_mul] at this
    rw [this]
    congr 1
    omega
  omega
noncomputable def betaParent {d m : ℕ} (U : Finset (ZMod (d * m))) (u : ZMod (d * m)) :
    ZMod (d * m) :=
  (betaParentVal U u : ZMod (d*m))
lemma betaParent_val {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hlu : 1 ≤ u.val / m) :
    (betaParent U u).val = betaParentVal U u := by
  have : NeZero (d*m) := ⟨by positivity⟩
  unfold betaParent
  exact ZMod.val_natCast_of_lt (betaParentVal_lt hd hm hlu)
lemma betaParent_level {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hlu : 1 ≤ u.val / m) :
    (betaParent U u).val / m = betaK U u := by
  rw [betaParent_val hd hm hlu]
  unfold betaParentVal
  have hφ : u.val % m < m := Nat.mod_lt _ hm
  rw [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hφ, Nat.zero_add]
lemma betaParent_level_lt {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hlu : 1 ≤ u.val / m) :
    (betaParent U u).val / m < u.val / m := by
  rw [betaParent_level hd hm hlu]
  have := betaK_le U u
  omega
lemma betaParent_val_lt {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hlu : 1 ≤ u.val / m) :
    (betaParent U u).val < u.val := by
  have hlev : (betaParent U u).val / m < u.val / m := betaParent_level_lt hd hm hlu
  exact sameblock_lt (x := betaParent U u) (y := u) hm hlev
variable {d m : ℕ}
def bEdge (U : Finset (ZMod (d * m))) (a b : ZMod (d * m)) : Prop :=
  b ∈ U ∧ 1 ≤ b.val / m ∧ a = betaParent U b
def bAdj (U : Finset (ZMod (d * m))) (a b : ZMod (d * m)) : Prop :=
  bEdge U a b ∨ bEdge U b a
def bReach (U : Finset (ZMod (d * m))) (a b : ZMod (d * m)) : Prop :=
  Relation.ReflTransGen (bAdj U) a b
lemma bReach_refl {U : Finset (ZMod (d * m))} (a : ZMod (d * m)) : bReach U a a :=
  Relation.ReflTransGen.refl
noncomputable instance bReachDecidable (U : Finset (ZMod (d * m))) (a b : ZMod (d * m)) :
    Decidable (bReach U a b) := Classical.dec _
noncomputable def bVerts (U : Finset (ZMod (d * m))) : Finset (ZMod (d*m)) :=
  U ∪ U.image (betaParent U)
noncomputable def betaBlock (U : Finset (ZMod (d * m))) (x : ZMod (d * m)) :
    Finset (ZMod (d * m)) :=
  (bVerts U).filter (fun y => @decide (bReach U x y) (bReachDecidable U x y))
lemma mem_betaBlock {U : Finset (ZMod (d * m))} {x y : ZMod (d * m)} :
    y ∈ betaBlock U x ↔ y ∈ bVerts U ∧ bReach U x y := by
  unfold betaBlock; simp_all
noncomputable def beta (U : Finset (ZMod (d * m))) : Finset (Finset (ZMod (d * m))) :=
  (bVerts U).image (betaBlock U)
lemma survivor_level_pos {d m : ℕ} (hd : 0 < d) {U : Finset (ZMod (d * m))}
    (hcanon : LevelCanonical d m U) {u : ZMod (d * m)} (hu : u ∈ U) : 1 ≤ u.val / m := by
  by_contra hlt
  push Not at hlt
  have hlt0 : u.val / m ≤ 0 := by omega
  have hmem : u ∈ U.filter (fun i => i.val / m ≤ 0) := by
    rw [Finset.mem_filter]; exact ⟨hu, hlt0⟩
  have hcanon0 : (U.filter (fun i => i.val / m ≤ 0)).card ≤ 0 := hcanon 0 hd
  have hempty : (U.filter (fun i => i.val / m ≤ 0)).card = 0 := Nat.le_zero.mp hcanon0
  rw [Finset.card_eq_zero] at hempty
  rw [hempty] at hmem
  exact absurd hmem (by simp)
noncomputable def bStep {d m : ℕ} (U : Finset (ZMod (d * m))) (x : ZMod (d * m)) :
    ZMod (d * m) :=
  if _hx : x ∈ U then betaParent U x else x
noncomputable def betaRoot {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) (x : ZMod (d * m)) : ZMod (d*m) :=
  if _hx : x ∈ U then betaRoot hd hm hcanon (betaParent U x) else x
termination_by x.val
decreasing_by exact betaParent_val_lt hd hm (survivor_level_pos hd hcanon _hx)
lemma betaBlock_nonempty {d m : ℕ} {U : Finset (ZMod (d * m))} {x : ZMod (d * m)}
    (hx : x ∈ bVerts U) : (betaBlock U x).Nonempty :=
  ⟨x, by rw [mem_betaBlock]; exact ⟨hx, bReach_refl x⟩⟩
end CriticalPortraits


