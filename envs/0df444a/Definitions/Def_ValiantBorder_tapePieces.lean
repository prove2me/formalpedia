-- Prove2me | Definitions.Def_ValiantBorder_tapePieces
-- name    : ValiantBorder_tapePieces
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:10:49.464653+00:00
-- url     : https://prove2.me/theorems/ffd861de-cd0e-4d8d-9dd8-af678b48d1ff
-- title:
--   A decomposition of a tape computation into pieces
-- statement:
--   The data specify a partition of the tape computation, its boundary bits, and the local tables for the resulting pieces. The requirements bound the number and size of the pieces and the cost of computing their products.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Pieces.lean#L134).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Pieces.lean#L134.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_groupEvaluator
/-! Based on Claude (Anthropic), *VP ≠ VNP over every field*, Theorems onecut and cut,
https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp .
This arrangement refactors the single-cut hypothesis from its quantitative amplification.
The upstream Lean source is copyright 2026 Anthropic, PBC and released under Apache 2.0,
https://www.apache.org/licenses/LICENSE-2.0. -/
namespace Nc.Cut

variable {Inp ι : Type} {D : ℕ}

/-- One step of a straight-line program with input coordinates `inp`. -/
def IsSlpStep (inp : ι → Inp → Fin D) (fn : ℕ → Inp → Fin D) (k : ℕ) : Prop :=
  (∃ i, fn k = inp i) ∨ (∃ c, fn k = fun _ => c) ∨
    ∃ i < k, ∃ j < k, ∃ φ : Fin D → Fin D → Fin D, ∀ x, fn k x = φ (fn i x) (fn j x)

end Nc.Cut
namespace Nc.Plus

/-- The unit has exactly one holder in the group `g`. -/
def OneIn {A mm : ℕ} {U : Type} (h0 h1 : U → Fin A) (a : Fin A → Fin mm) (g : Fin mm) (id : U) : Prop :=
  (a (h0 id) = g ∧ a (h1 id) ≠ g) ∨ (a (h0 id) ≠ g ∧ a (h1 id) = g)

instance {A mm : ℕ} {U : Type} (h0 h1 : U → Fin A) (a : Fin A → Fin mm) (g : Fin mm) (id : U) :
    Decidable (OneIn h0 h1 a g id) := by unfold OneIn; infer_instance

end Nc.Plus
namespace Nc
open Finset
variable {U W : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
/-- Common contents of units: empty outside `New`. -/
def Common (e : W) (New : Finset U) : Finset (U → W) := univ.filter fun z => ∀ id, id ∉ New → z id = e


end Nc
namespace Nc.Dl
open NS1 Finset Nc.G Nc.Cut
variable {A : Type} [CommRing A] {K A' E U0 U1 mm : ℕ} {M : Sys A (K + K + A') E}
/-- The straight-line program of a plan: digits `Fin D`; the numbers of units and the outcomes are inputs. -/
structure SlpTab (P : G.Plan M U0 U1) (grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm) (D pS : ℕ) where
  /-- the functions -/
  fn : ℕ → NN K U0 × (M.N → Fin U1) → Fin D
  /-- inputs -/
  inp : (Fin (K + K) × Fin (K + K)) ⊕ M.N → NN K U0 × (M.N → Fin U1) → Fin D
  inpN : ∀ a b x, (inp (.inl (a, b)) x : ℕ) = x.1 a b
  inpO : ∀ ν x, (inp (.inr ν) x : ℕ) = x.2 ν
  step : ∀ k < pS, IsSlpStep inp fn k
  /-- is a unit current in the end? -/
  kcur : G.Uid (K + K) U0 M.N U1 → Fin pS
  hcur : ∀ id x, (fn (kcur id) x : ℕ) = if id ∈ P.cur x.1 x.2 E then 1 else 0
  /-- is a unit cut? -/
  kcut : G.Uid (K + K) U0 M.N U1 → Fin pS
  hcut : ∀ id x, (fn (kcut id) x : ℕ) =
    if id ∈ P.cur x.1 x.2 E ∧ grp x.1 x.2 (G.hold0 M.np id) ≠ grp x.1 x.2 (G.hold1 M.np id) then 1 else 0
  /-- is a unit given in a slot? -/
  kcons : M.Z → G.Uid (K + K) U0 M.N U1 → Fin pS
  hcons : ∀ z id x, (fn (kcons z id) x : ℕ) = if id ∈ P.cons x.1 x.2 z then 1 else 0
  /-- number of units of a move -/
  knum : Fin E → Fin pS
  hnum : ∀ y x, (fn (knum y) x : ℕ) = P.num x.1 x.2 y
  /-- conditions: the outcome of a move is good; the numbers of units are valid -/
  kcond : Option (Fin E) → Fin pS
  /-- validity -/
  valid : NN K U0 → Prop
  hgood : ∀ y x, (fn (kcond (some y)) x : ℕ) = 1 ↔ P.good x.1 x.2 y
  hvalid : ∀ x, (fn (kcond none) x : ℕ) = 1 ↔ valid x.1
  /-- groups -/
  kgrp : Fin (K + K + A') → Fin pS
  hgrp : ∀ p x, (fn (kgrp p) x : ℕ) = grp x.1 x.2 p


end Nc.Dl
namespace Nc.Tow
open Finset Nc.G
variable (F : Type) [CommRing F]
/-- The table of a role of a relay. -/
def relTab (p : Fin 3) (X : {e : Unit // (0 : Fin 3) = p ∨ (2 : Fin 3) = p} → Bool)
    (g : ∀ ν : {ν : Bool // (if ν then (1 : Fin 3) else 0) = p ∨ (if ν then (2 : Fin 3) else 1) = p},
      Fin 1 → Bool) : F :=
  if h0 : p = 0 then if X ⟨(), Or.inl h0.symm⟩ = g ⟨false, by simp [h0]⟩ 0 then 1 else 0
  else if h1 : p = 1 then if g ⟨false, by simp [h1]⟩ 0 = g ⟨true, by simp [h1]⟩ 0 then 1 else 0
  else if h2 : p = 2 then if g ⟨true, by simp [h2]⟩ 0 = X ⟨(), Or.inr h2.symm⟩ then 1 else 0
  else 1

/-- The relay: a bit shared by the roles 0 and 2 is led through the role 1. -/
def relay : Law F where
  Ro := Fin 3
  Sl := Unit
  Cn := Bool
  I := Unit
  a _ := 0
  b _ := 2
  ab _ := by decide
  c ν := if ν then 1 else 0
  d ν := if ν then 2 else 1
  cd ν := by cases ν <;> decide
  lam := 0
  lab _ i := i.elim0
  lab_inj _ _ _ := rfl
  len _ _ := 1
  tab p _ X g := relTab F p X g
  law X := by
    classical
    rw [Fintype.sum_unique]
    have e : (fun g : ∀ _ : Bool, Fin 1 → Bool => ∏ p : Fin 3, relTab F p (fun e => X p e) fun ν => g ν) =
        fun g => if g false 0 = X 0 () ∧ g true 0 = X 0 () ∧ X 0 () = X 2 () then 1 else 0 := by
      funext g
      rw [Fin.prod_univ_three]
      simp only [relTab, Fin.isValue, dite_true, if_true, one_ne_zero, dite_false, reduceDIte]
      have h20 : ¬ (2 : Fin 3) = 0 := by decide
      have h21 : ¬ (2 : Fin 3) = 1 := by decide
      simp only [h20, h21, dite_false]
      have key : ∀ x y u v : Bool, ((if x = u then (1 : F) else 0) * (if u = v then 1 else 0) *
          if v = y then 1 else 0) = if u = x ∧ v = x ∧ x = y then 1 else 0 := by
        intro x y u v
        cases x <;> cases y <;> cases u <;> cases v <;> simp
      exact key _ _ _ _
    rw [show (∑ g : ∀ _ : Bool, Fin 1 → Bool, ∏ p : Fin 3, relTab F p (fun e => X p e) fun ν => g ν) =
      ∑ g : ∀ _ : Bool, Fin 1 → Bool, if g false 0 = X 0 () ∧ g true 0 = X 0 () ∧ X 0 () = X 2 () then (1 : F) else 0 from
        congrArg (fun f => ∑ g, f g) e]
    by_cases h : X 0 () = X 2 ()
    · rw [if_pos fun _ => h, Finset.sum_eq_single fun _ _ => X 0 ()]
      · simp [h]
      · intro g _ hg
        rw [if_neg]
        rintro ⟨h1, h2, -⟩
        apply hg
        funext ν k
        have hk : k = 0 := Subsingleton.elim _ _
        subst hk
        cases ν
        · exact h1
        · exact h2
      · intro hn; exact absurd (mem_univ _) hn
    · rw [if_neg fun hh => h (hh ()), Finset.sum_eq_zero]
      intro g _
      rw [if_neg fun hh => h hh.2.2]
  conn _ _ _ _ := rfl


end Nc.Tow
namespace Nc.Tow
open Finset Nc.G
/-- The roles of the relay and of finitely many laws. -/
noncomputable def kindList (F : Type) [CommRing F] (laws : List (Law F)) : List (Σ L : Law F, L.Ro) :=
  (relay F :: laws).flatMap fun L => (univ : Finset L.Ro).toList.map fun p => ⟨L, p⟩


end Nc.Tow
namespace Paper
 
noncomputable def goodBound (C₁ : ℝ) (a₁ : ℕ) : ℕ := ⌊2 * C₁ * (a₁ : ℝ) ^ 2⌋₊
end Paper
namespace Paper
open Finset Nc Nc.G Nc.Dl Nc.Tow Nc.Vp
open NS1 (lg)
variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
open Classical in
/-- The pieces of Proposition prop:pieces for the scale v, K blocks of T steps and the parameter k, with the exponent
C and the list kinds of roles that may occur in moves. An input word is cut into K consecutive parts of ℓ ≤ T symbols;
ρ gives, for every node and side of a tape, the first and the last node that take the symbols of the node, n gives the
numbers of units, o the outcomes, and grp says in which piece a node is. At the beginning a node holds at most load
units. -/
structure PieceCut (kinds : List (Σ L : G.Law A, L.Ro)) (mu : Nc.Letter S Unit Γ → Matrix Q Q A)
    (b G₁ v K T k C : ℕ) where
  /-- bits for a symbol -/
  c : ℕ
  /-- the code of symbols -/
  cb : Option Γ → Fin c → Bool
  cb_inj : Function.Injective cb
  c_le : c ≤ C
  /-- bits of a unit -/
  ub : ℕ
  ub_pos : 0 < ub
  /-- the bound for units between two nodes -/
  U0 : ℕ
  /-- the bound for units at a node at the beginning -/
  load : ℕ
  /-- units have at most T bits, and a node starts with few of them -/
  unit_le : ub ≤ T ∧ load * ub ≤ T * lg v ^ C
  /-- the number of further nodes -/
  A' : ℕ
  /-- the number of moves -/
  E : ℕ
  /-- a bound for outcomes -/
  U1 : ℕ
  U1_pos : 0 < U1
  /-- the number of pieces -/
  num : ℕ
  /-- the digits of the program -/
  D : ℕ
  /-- the steps of the program -/
  steps : ℕ
  /-- the moves -/
  sys : Sys A (K + K + A') E
  /-- the plan -/
  plan : G.Plan sys U0 U1
  /-- a bound for the units of one move -/
  cap : ℕ
  /-- the plan is causal and gives only current units between the ends of their slots -/
  ok : plan.Ok cap
  /-- is the move a law move? -/
  isLaw : Fin E → Bool
  relay_kind : ∀ x, isLaw x = false → sys.kind x = relay A
  /-- what good means -/
  good_iff : ∀ n o x, plan.good n o x ↔ if isLaw x then
      b * ∑ ν : (sys.kind x).Cn, (o ⟨x, ν⟩).val ^ 2 ≤ G₁ * plan.num n o x ^ 2 ∧
        ∀ ν : (sys.kind x).Cn, plan.num n o x ≤ o ⟨x, ν⟩
    else ∀ ν : (sys.kind x).Cn, (o ⟨x, ν⟩).val = plan.num n o x
  /-- every possible outcome is good -/
  poss_good : ∀ n o x, plan.Poss n o ub x → plan.good n o x
  /-- the piece of a node -/
  grp : Dl.NN K U0 → (sys.N → Fin U1) → Fin (K + K + A') → Fin num
  /-- the program that computes units, moves, good outcomes and pieces from n and o -/
  tab : SlpTab plan grp D steps
  /-- it checks that no node has more than load units -/
  tab_valid : ∀ n, tab.valid n ↔ ∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ load
  /-- its numbers have room for the units, the outcomes and the pieces -/
  digits : U0 < D ∧ U1 ≤ D ∧ num ≤ D ∧ 1 < D
  /-- every role at a move is from the fixed list, so its numbers of channels and slots are bounded -/
  kinds_mem : ∀ r : sys.R, ⟨sys.kind r.1, r.2⟩ ∈ kinds
  outcomes_le : Fintype.card sys.N ≤ v ^ C
  num_le : num ≤ k * lg v ^ C
  blocks_le : ∀ n o, (∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ load) → (∀ x, plan.good n o x) → ∀ g,
    (univ.filter fun p : Fin (K + K) => grp n o (Fin.castAdd A' p) = g).card * k ≤ C * K
  cut_le : ∀ n o, (∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ load) → (∀ x, plan.good n o x) → ∀ g,
    ((plan.cur n o E).filter (Nc.Plus.OneIn (hold0 sys.np) (hold1 sys.np) (grp n o) g)).card * ub * v ^ 300 ≤
      K * T * lg v ^ C
  all_le : ∀ n o, (∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ load) → (∀ x, plan.good n o x) → ∀ g,
    (evG grp n o g + pdG plan grp n o g) * ub * k ≤ K * T * lg v ^ C
  steps_le : D ≤ v ^ C ∧ steps ≤ v ^ C ∧ K + K + A' ≤ v ^ C ∧ E ≤ v ^ C ∧ U0 ≤ v ^ C ∧ U1 ≤ v ^ C
  value : ∀ (i e : Q) (u : Unit → List Γ) (ℓ : ℕ), ℓ ≤ T → (u ()).length ≤ K * ℓ →
    Nc.runVal mu i e (K * T) u = ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
      ∑ ρ : Option S → Fin (K + K) → Nc.Cut.RowData (K + K), if Nc.Cut.ValidRows ρ then
        ∑ n : Dl.NN K U0, if ∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ load then
          ∑ o : sys.N → Fin U1, if ∀ x, plan.good n o x then
            ∑ b ∈ Nc.Common (none : Nc.UW ub) (Nc.cutUnits (hold0 sys.np) (hold1 sys.np) (grp n o) (plan.cur n o E)),
              ∏ g, grpVal mu T cb plan q (Nc.Cut.parts ℓ (u ())) ρ n o (grp n o) g b
          else 0
        else 0
      else 0
    else 0


end Paper


