-- Prove2me | Definitions.Def_CountedRecursion_RecursionDefs
-- name    : CountedRecursion_RecursionDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:53:33.624196+00:00
-- url     : https://prove2.me/theorems/fa3dc740-09a3-45d6-ac94-f8fab1222e19
-- title:
--   Recursion Defs
-- statement:
--   Definitions and structural lemmas for Recursion Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RecursionDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CliqueLevelsStatement
import Theorems.Thm_Eight_Level_rho_ge
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
structure Setting (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data) : Prop where
  is : D.Is ρ c
  short : ∀ lam tr i, D.cap lam tr i ≤ 2 * lam
  x₀_ge : 18 ≤ x₀
  x₀_c : c + 5 ≤ 2 ^ x₀
def indexAt (D : PiecesCounted.Data) (lam j : ℕ) : ℤ := ((D.fam lam).I.sort).getD j 0
def piecesOf (D : PiecesCounted.Data) (c : ℕ) : PiecesF where
  cnt _ lam := #(D.fam lam).I
  d _ lam := (D.fam lam).d.toNat
  cap tr _ lam j := D.cap lam tr (indexAt D lam j)
  top q := if q.2.2.2.2.length = D.cap q.2.2.1.length q.1.2 (indexAt D q.2.2.1.length q.2.1.2) then
    D.fn q.2.2.1.length q.1.2 false (indexAt D q.2.2.1.length q.2.1.2) (PiecesCounted.toBits _ q.2.2.1, PiecesCounted.toBits _ q.2.2.2.1) q.2.2.2.2 else 0
  bot q := if q.2.2.2.2.length = D.cap q.2.2.1.length q.1.2 (indexAt D q.2.2.1.length q.2.1.2) then
    D.fn q.2.2.1.length q.1.2 true (indexAt D q.2.2.1.length q.2.1.2) (PiecesCounted.toBits _ q.2.2.1, PiecesCounted.toBits _ q.2.2.2.1) q.2.2.2.2 else 0
  need _ _ := 0
  bits _ lam := (2 * lam) ^ c
  m := 1
def listsOf (D : PiecesCounted.Data) (lam : ℕ) : Lists :=
  ((D.fam lam).I.sort, ((D.fam lam).I.sort).map fun i => D.cap lam false i, ((D.fam lam).I.sort).map fun i => D.cap lam true i)
noncomputable def patternNet (D : PiecesCounted.Data) (c g : ℕ) (tr : Bool) (lam y : ℕ) (W : ℕ → List Bool → ℤ) : Net (nParts g g tr) :=
  ofNetwork (gridN (piecesOf D c) [()] g g tr 0 lam y fun w θ => W w.val (List.ofFn θ).flatten) fun _ => g ^ 3 * lam
def mkParent (D : PiecesCounted.Data) (K g lam B : ℕ) (tr : Bool) (y x : ℕ) : Parent := ((unary K, unary g), (unary lam, unary B), listsOf D lam, (tr, y, x))
def Xi (g lam B : ℕ) : ℕ := g ^ 2 * (lam + B)
def answersOf (K lam : ℕ) (W : ℕ → List Bool → ℤ) : TableQuery → Option Ans := fun q => (tables K lam W q).map Sum.inl
def readTables (f : TableQuery → Option Ans) : ℕ → List Bool → ℤ := fun w z => asInt ((f (w, z)).getD (.inl 0))
def Fits (x₀ : ℕ) (a : Ctx) (f : TableQuery → Option Ans) : Prop :=
  1 ≤ cLam a ∧ 1 ≤ cB a ∧ ∃ W : ℕ → List Bool → ℤ, (∀ w < Levels.Gen.K x₀ (cLev a), ∀ z ∈ words ((Levels.Gen.K x₀ (cLev a) - 1) * cLam a), |W w z| < 2 ^ cB a) ∧ f = answersOf (Levels.Gen.K x₀ (cLev a)) (cLam a) W
def readyOf (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) : Ready :=
  (((((h, (unary (2 ^ (3 * (hLev h - 1) + x₀)), unary (Levels.Gen.K x₀ (hLev h - 1)))), (listsOf D (hLam h)).1), (D.fam (hLam h)).d), (listsOf D (hLam h)).2.1), (listsOf D (hLam h)).2.2)
noncomputable def groupTables (D : PiecesCounted.Data) (c : ℕ) (p : Parent) (L : ℕ) (W : ℕ → List Bool → ℤ) : ℕ → List Bool → ℤ := fun γ Θ =>
  if h : γ < pK p then
    (Value.groupClique asked.under (netInput (patternNet D c (pG p) (pTr p) (pLam p) (pY p) W) (netP p) (netB c p)) (patternNet D c (pG p) (pTr p) (pLam p) (pY p) W) (Nat.zero_lt_of_lt h) (pX p) L).W ⟨γ, h⟩ Θ
  else 0
noncomputable def spec (D : PiecesCounted.Data) (c x₀ : ℕ) (Bound : Ctx → Prop) : Tower.Spec Ctx TableQuery Ans where
  lev := cLev
  Good a f := Bound a ∧ Fits x₀ a f
  val a f := .inl (clique (Levels.Gen.K x₀ (cLev a)) (cLam a) fun w => readTables f w.val).value
  Child a _ a' := 1 ≤ cLev a ∧ ∃ y x : ℕ, y < nPatterns (readyOf D x₀ a.1) ∧
    (List.range (rK (readyOf D x₀ a.1) ^ rG (readyOf D x₀ a.1))).find? (fun x' => goodData (searchInput c (readyOf D x₀ a.1, y), x')) = some x ∧ a' = child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))
  tab a' f := answersOf (pK (parentOf a')) (cLam a') (groupTables D c (parentOf a') (cLam a') (readTables f))
noncomputable def boundsDown (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ → ℕ × ℕ
  | 0 => (lam, B)
  | k + 1 =>
    (⌊((ρ + 3 * Levels.Gen.zeta (l - (k + 1))) * ((Levels.Gen.g x₀ (l - (k + 1)) : ℝ) ^ 4 * (boundsDown ρ c x₀ l lam B k).1) +
        (c : ℝ) / 4 * (Levels.Gen.g x₀ (l - (k + 1)) : ℝ) ^ 4 * Real.logb 2 (2 * (boundsDown ρ c x₀ l lam B k).1) + (Levels.Gen.K x₀ (l - (k + 1)) : ℝ) ^ 2) / (Levels.Gen.K x₀ (l - (k + 1)) : ℝ) ^ 2⌋₊,
     bitsOut (Levels.Gen.K x₀ (l - (k + 1))) (Levels.Gen.g x₀ (l - (k + 1))) (Levels.Gen.g x₀ (l - (k + 1)) ^ 3 * (boundsDown ρ c x₀ l lam B k).1)
       (bitsOne c (Levels.Gen.g x₀ (l - (k + 1))) (boundsDown ρ c x₀ l lam B k).1 (boundsDown ρ c x₀ l lam B k).2))
noncomputable def lamAt (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ := (boundsDown ρ c x₀ l lam B (l - j)).1
noncomputable def bitsAt (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ := (boundsDown ρ c x₀ l lam B (l - j)).2
def InBounds (ρ : ℝ) (c x₀ l lam B : ℕ) (a : Ctx) : Prop := cLev a ≤ l ∧ cLam a ≤ lamAt ρ c x₀ l lam B (cLev a) ∧ cB a ≤ bitsAt ρ c x₀ l lam B (cLev a)
noncomputable def lamMax (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ := (range (l + 1)).sup fun j => lamAt ρ c x₀ l lam B j
def piecesUpTo (D : PiecesCounted.Data) (Lam : ℕ) : PieceQuery → Option Ans := fun g => if g.1.length ≤ Lam then D.oracle g else none
def askCost (c lam : ℕ) : ℕ := PiecesCounted.steps c lam + 2
def solPrices (c tc tq : ℕ) : SolQuery → ℕ := Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) (PiecesCounted.price c))
def upPrices (c tq : ℕ) : UpQuery → ℕ := Sum.elim (fun _ => tq) (PiecesCounted.price c)
def ListsAgree : Prop := ∀ (D : PiecesCounted.Data) (c lam : ℕ), (∀ tr i, D.cap lam tr i ≤ 2 * lam) →
  (listsAsPieces (listsOf D lam)).cnt 0 lam = (piecesOf D c).cnt 0 lam ∧ ∀ tr, ∀ j < #(D.fam lam).I, (listsAsPieces (listsOf D lam)).cap tr 0 lam j = (piecesOf D c).cap tr 0 lam j
def SolverBase : Prop := ∃ C₅ : ℕ, ∀ (D : PiecesCounted.Data) (c x₀ : ℕ) (Bound : Ctx → Prop) (gl : PieceQuery → Option Ans) (a : Ctx) (f : TableQuery → Option Ans), Fits x₀ a f → cLev a = 0 → ∀ tc tq : ℕ,
  (solver c x₀).Within ((spec D c x₀ Bound).oracle gl a f) (solPrices c tc tq) a (2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * cLam a) * (2 ^ x₀ * (tq + 1) + 1)) ((2 ^ x₀ * (cLam a + cB a)) ^ C₅) ((spec D c x₀ Bound).val a f)
def Expansion : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (g lam : ℕ) (W : ℕ → List Bool → ℤ) (tr : ℕ → Bool), 2 ≤ g → 1 ≤ lam →
  (D.fam lam).d ^ nRectG g g * (clique (g * g) lam fun w => W w.val).value = ∑ y ∈ range (#(D.fam lam).I ^ nRectG g g), (patternNet D c g (tr y) lam y W).value
def PatternsFew : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ g lam B : ℕ, 2 ≤ g → 1 ≤ lam → 1 ≤ B → 4 * nRectG g g ≤ g ^ 4 ∧ (#(D.fam lam).I ^ nRectG g g) ^ 4 ≤ Xi g lam B ^ (c * g ^ 4)
def BothNetworks : Prop := ∀ c : ℕ, ∃ C₂ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (K g lam B y x tq Lam : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ), 2 ≤ g → K ≤ g → 1 ≤ lam → lam ≤ Lam → 1 ≤ B →
  (∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) → y < #(D.fam lam).I ^ nRectG g g → x < K ^ g →
    (patternNet D c g tr lam y W).Is (g ^ 3 * lam) (bitsOne c g lam B) ∧
    (∀ a b, a ≠ b → (patternNet D c g tr lam y W).c a b ≤ g ^ 2 * lam) ∧
    netData c (mkParent D K g lam B tr y x) = ((unary K, unary g), netInput (patternNet D c g tr lam y W) (g ^ 3 * lam) (bitsOne c g lam B)) ∧
    ∀ (q : NetQuery) (v : ℤ), netOracle (patternNet D c g tr lam y W) q = some v →
      (gridProcsData c).answer.Within (Sum.elim (answersOf (g * g) lam W) (piecesUpTo D Lam)) (upPrices c tq) (mkParent D K g lam B tr y x, q) ((askCost c lam + tq) * Xi g lam B ^ C₂) (Xi g lam B ^ C₂) v
def pieceValue (D : PiecesCounted.Data) (lam : ℕ) (i : ℤ) (s : List Bool × List Bool × List Bool × List Bool) : ℤ :=
  (D.fam lam).A i (PiecesCounted.toBits lam s.1) (PiecesCounted.toBits lam s.2.1) (PiecesCounted.toBits lam s.2.2.1) (PiecesCounted.toBits lam s.2.2.2)
def PairIsProduct : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (g lam y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ), 2 ≤ g → 1 ≤ lam → y < #(D.fam lam).I ^ nRectG g g →
  ∀ a b : Fin (nParts g g tr), a < b → ∀ z ∈ (patternNet D c g tr lam y W).S a, ∀ z' ∈ (patternNet D c g tr lam y W).S b,
    (patternNet D c g tr lam y W).Ψ a b z z' = if straightOK g tr lam ((a.val, b.val), (z, z')) = true then
      ∏ j ∈ range (g * g), (if j / g < j % g then pieceValue D lam (indexAt D lam (digG (piecesOf D c) g tr 0 lam y (tri a.val b.val) (tri (j / g) (j % g)))) (rectStrings g tr lam ((a.val, b.val), (z, z')) (j / g) (j % g)) else 1)
    else 0
def TotalsAre : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (g lam y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ), 2 ≤ g → 1 ≤ lam →
  (patternNet D c g tr lam y W).U = totalG (listsAsPieces (listsOf D lam)) g g tr 0 lam y
def SmallerTotal : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ g lam y : ℕ, 2 ≤ g → 1 ≤ lam → y < #(D.fam lam).I ^ nRectG g g →
  ((min (totalG (listsAsPieces (listsOf D lam)) g g false 0 lam y) (totalG (listsAsPieces (listsOf D lam)) g g true 0 lam y) : ℕ) : ℝ) ≤ (g : ℝ) ^ 4 * lam * (ρ + 1 / g) + (c : ℝ) / 4 * (g : ℝ) ^ 4 * Real.logb 2 (2 * lam)
def CaseTwoApplies : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (l lam y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ), 1 ≤ lam → y < #(D.fam lam).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) →
  AppRunningTime.Cases (Levels.Gen.K x₀ l) (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) tr) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) (patternNet D c (Levels.Gen.g x₀ l) tr lam y W).c
def LabelBound : Prop := ∀ (ρ : ℝ) (c x₀ l lam U : ℕ), 1 / 2 ≤ ρ → 18 ≤ x₀ → 1 ≤ lam → (U : ℝ) ≤ (Levels.Gen.g x₀ l : ℝ) ^ 4 * lam * (ρ + 1 / Levels.Gen.g x₀ l) + (c : ℝ) / 4 * (Levels.Gen.g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * lam) →
  (Levels.Gen.K x₀ l : ℝ) ^ 2 * AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) U ≤
    (ρ + 3 * Levels.Gen.zeta l) * ((Levels.Gen.g x₀ l : ℝ) ^ 4 * lam) + (c : ℝ) / 4 * (Levels.Gen.g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * lam) + (Levels.Gen.K x₀ l : ℝ) ^ 2
def LabelCrude : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (l lam y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ), 1 ≤ lam →
  AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) (patternNet D c (Levels.Gen.g x₀ l) tr lam y W).U ≤ Levels.Gen.g x₀ l ^ 4 * lam + 1
def CrudeBounds : Prop := ∀ c x₀ l lam B L : ℕ, 18 ≤ x₀ → 1 ≤ lam → 1 ≤ B → L ≤ Levels.Gen.g x₀ l ^ 4 * lam + 1 →
  bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * lam) (bitsOne c (Levels.Gen.g x₀ l) lam B) ≤ Levels.Gen.g x₀ l ^ 4 * lam + Levels.Gen.g x₀ l ^ 2 * bitsOne c (Levels.Gen.g x₀ l) lam B ∧
  Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * lam + bitsOne c (Levels.Gen.g x₀ l) lam B) ≤ Xi (Levels.Gen.g x₀ l) lam B ^ (c + 4) ∧
  Levels.Gen.K x₀ l * (L + bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * lam) (bitsOne c (Levels.Gen.g x₀ l) lam B)) ≤ Xi (Levels.Gen.g x₀ l) lam B ^ (c + 5)
def ChildIsGood : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (Bound : Ctx → Prop) (a a' : Ctx) (f : TableQuery → Option Ans) (l : ℕ), Fits x₀ a f → cLev a = l + 1 → (spec D c x₀ Bound).Child a f a' →
  cLev a' = l ∧ Fits x₀ a' ((spec D c x₀ Bound).tab a' f) ∧
  pY (parentOf a') < nPatterns (readyOf D x₀ a.1) ∧
  (spec D c x₀ Bound).val a' ((spec D c x₀ Bound).tab a' f) = .inl (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, pY (parentOf a'))) (cLam a) (pY (parentOf a')) (readTables f)).value ∧
  (Levels.Gen.K x₀ l : ℝ) ^ 2 * cLam a' ≤ (ρ + 3 * Levels.Gen.zeta l) * ((Levels.Gen.g x₀ l : ℝ) ^ 4 * cLam a) + (c : ℝ) / 4 * (Levels.Gen.g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * cLam a) + (Levels.Gen.K x₀ l : ℝ) ^ 2 ∧
  cB a' = bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))
def ProcedureCost : Prop := ∀ c : ℕ, ∃ C : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (Bound : Ctx → Prop) (a a' : Ctx) (f : TableQuery → Option Ans) (l : ℕ), Fits x₀ a f → cLev a = l + 1 → (spec D c x₀ Bound).Child a f a' →
  ∀ (q : TableQuery) (v : Ans), (spec D c x₀ Bound).tab a' f q = some v → ∀ tq Lam : ℕ, cLam a ≤ Lam →
    (procedure c).Within (Sum.elim f (piecesUpTo D Lam)) (upPrices c tq) (a', q)
      (2 ^ (Levels.Gen.g x₀ l ^ 3 * cLam a * (2 * Levels.Gen.g x₀ l / Levels.Gen.K x₀ l)) * ((askCost c (cLam a) + tq) * Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C)) (Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C) v
def SolverStep : Prop := ∀ c : ℕ, ∃ C₃ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (Bound : Ctx → Prop) (a : Ctx) (f : TableQuery → Option Ans) (l : ℕ), Fits x₀ a f → cLev a = l + 1 →
  (∀ a', (spec D c x₀ Bound).Child a f a' → size a' ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₃) ∧
  ∀ tc tq Lam : ℕ, cLam a ≤ Lam → (solver c x₀).Within ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (solPrices c tc tq) a
    (#(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) * (Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₃ * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + tc) + (2 * #(D.fam (cLam a)).I + 2) * askCost c (cLam a) + Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₃)
    (Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₃) ((spec D c x₀ Bound).val a f)
def BothNetworksFrom : Prop := PairIsProduct → ListsAgree → BothNetworks
def ChildIsGoodFrom : Prop := GroupingWithCall → LabelLengthIsL → EntryCostExplicit → ValueIsKept → BothNetworks → TotalsAre → SmallerTotal → CaseTwoApplies → LabelBound → ChildIsGood
def ProcedureCostFrom : Prop := GroupingWithCall → LabelLengthIsL → CaseTwoApplies → EntryCostExplicit → BothNetworks → LabelCrude → CrudeBounds → QueryMachines.StSubstWithin → ProcedureCost
def SolverStepFrom : Prop := NumbersRun → Expansion → PatternsFew → GroupingWithCall → LabelLengthIsL → ValueIsKept → BothNetworks → CaseTwoApplies → CrudeBounds → QueryMachines.StSubstWithin → SolverStep
noncomputable def xiAt (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ := Xi (Levels.Gen.g x₀ j) (lamAt ρ c x₀ l lam B (j + 1)) (bitsAt ρ c x₀ l lam B (j + 1))
noncomputable def patternsAt (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ := ((2 * lamAt ρ c x₀ l lam B (j + 1)) ^ c) ^ nRectG (Levels.Gen.g x₀ j) (Levels.Gen.g x₀ j)
noncomputable def solverOwn (C : ℕ) (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ → ℕ
  | 0 => 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0) * (2 ^ x₀ + 1)
  | j + 1 => patternsAt ρ c x₀ l lam B j * (xiAt ρ c x₀ l lam B j ^ C * Levels.Gen.K x₀ j ^ Levels.Gen.g x₀ j) + (2 * (2 * lamAt ρ c x₀ l lam B (j + 1)) ^ c + 2) * askCost c (lamAt ρ c x₀ l lam B (j + 1)) + xiAt ρ c x₀ l lam B j ^ C
noncomputable def solverCalls (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => patternsAt ρ c x₀ l lam B j
noncomputable def solverAsks (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ → ℕ
  | 0 => 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0) * 2 ^ x₀
  | _ + 1 => 0
noncomputable def solverCost (C : ℕ) (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ → ℕ → ℕ → ℕ := Tower.shapeS (solverOwn C ρ c x₀ l lam B) (solverCalls ρ c x₀ l lam B) (solverAsks ρ c x₀ l lam B)
noncomputable def entryAsks (C : ℕ) (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ :=
  2 ^ (Levels.Gen.g x₀ j ^ 3 * lamAt ρ c x₀ l lam B (j + 1) * (2 * Levels.Gen.g x₀ j / Levels.Gen.K x₀ j)) * xiAt ρ c x₀ l lam B j ^ C
noncomputable def entryOwn (C : ℕ) (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ := entryAsks C ρ c x₀ l lam B j * askCost c (lamAt ρ c x₀ l lam B (j + 1))
noncomputable def entryCost (C : ℕ) (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ → ℕ → ℕ := Tower.shapeI (entryOwn C ρ c x₀ l lam B) (entryAsks C ρ c x₀ l lam B)
noncomputable def roomAll (C : ℕ) (ρ : ℝ) (c x₀ l lam B : ℕ) : ℕ := ∑ j ∈ range (l + 1), (Levels.Gen.K x₀ j * (lamAt ρ c x₀ l lam B j + bitsAt ρ c x₀ l lam B j)) ^ C
def RecursionMeets : Prop := ∀ c : ℕ, ∃ C : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ l lam B : ℕ, 1 ≤ lam → 1 ≤ B →
  (spec D c x₀ (InBounds ρ c x₀ l lam B)).Meets (piecesUpTo D (lamMax ρ c x₀ l lam B)) (PiecesCounted.price c) (solver c x₀) (procedure c) (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B)
def RecursionMeetsFrom : Prop := SolverBase → SolverStep → ProcedureCost → ChildIsGood → RecursionMeets
noncomputable def sizeBound (x₀ C₀ l lam B : ℕ) : ℝ := ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ (C₀ * Levels.Gen.K x₀ l)
noncomputable def timeBound (ρ : ℝ) (x₀ C₀ l lam B : ℕ) : ℝ := (2 : ℝ) ^ (Levels.Gen.e ρ x₀ l * (Levels.Gen.K x₀ l : ℝ) ^ 2 * lam) * ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ (C₀ * Levels.Gen.K x₀ l ^ 2)
noncomputable def baseAt (ρ : ℝ) (c x₀ l lam B j : ℕ) : ℕ := Levels.Gen.K x₀ j * (lamAt ρ c x₀ l lam B j + bitsAt ρ c x₀ l lam B j)
structure Numbers (ρ : ℝ) (c x₀ lam B : ℕ) : Prop where
  rho_ge : 1 / 2 ≤ ρ
  rho_lt : ρ < 1
  c_pos : 1 ≤ c
  x₀_ge : 18 ≤ x₀
  x₀_c : c + 5 ≤ 2 ^ x₀
  lam_pos : 1 ≤ lam
  B_pos : 1 ≤ B
def ChainLabel : Prop := ∀ (ρ : ℝ) (c x₀ l lam B j : ℕ), Numbers ρ c x₀ lam B → j < l →
  1 ≤ lamAt ρ c x₀ l lam B j ∧ 1 ≤ bitsAt ρ c x₀ l lam B j ∧ lamAt ρ c x₀ l lam B j ≤ Levels.Gen.g x₀ j ^ 4 * lamAt ρ c x₀ l lam B (j + 1) + 1 ∧
  (Levels.Gen.K x₀ j : ℝ) ^ 2 * lamAt ρ c x₀ l lam B j ≤ (ρ + 3 * Levels.Gen.zeta j) * ((Levels.Gen.g x₀ j : ℝ) ^ 4 * lamAt ρ c x₀ l lam B (j + 1)) +
    (c : ℝ) / 4 * (Levels.Gen.g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * lamAt ρ c x₀ l lam B (j + 1)) + (Levels.Gen.K x₀ j : ℝ) ^ 2
def ChainBase : Prop := ∀ (ρ : ℝ) (c x₀ l lam B j : ℕ), Numbers ρ c x₀ lam B → j < l → baseAt ρ c x₀ l lam B j ≤ baseAt ρ c x₀ l lam B (j + 1) ^ (c + 5)
def ChainLevels : Prop := ∀ c x₀ l k : ℕ, 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → k ≤ l → 2 ^ k * (c + 5) ^ k * Levels.Gen.K x₀ (l - k) ^ 2 ≤ Levels.Gen.K x₀ l ^ 2 ∧ (c + 5) ^ l ≤ Levels.Gen.K x₀ l
def ChainExponent : Prop := ∀ (ρ : ℝ) (c x₀ l lam B j : ℕ), Numbers ρ c x₀ lam B → j < l →
  Levels.Gen.e ρ x₀ j * (Levels.Gen.K x₀ j : ℝ) ^ 2 * lamAt ρ c x₀ l lam B j + 3 * ((Levels.Gen.K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) / Levels.Gen.K x₀ j ≤
    Levels.Gen.e ρ x₀ (j + 1) * (Levels.Gen.K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1) + (c : ℝ) / 4 * (Levels.Gen.K x₀ (j + 1) : ℝ) ^ 2 * Real.logb 2 (2 * lamAt ρ c x₀ l lam B (j + 1)) + (Levels.Gen.K x₀ j : ℝ) ^ 2
def ChainBaseFrom : Prop := ChainLabel → CrudeBounds → ChainBase
def ChainExponentFrom : Prop := ChainLabel → Levels.Gen.PartA → ChainExponent
noncomputable def levelBound (ρ : ℝ) (c x₀ C₀ l lam B j : ℕ) : ℝ := timeBound ρ x₀ C₀ j (lamAt ρ c x₀ l lam B j) (bitsAt ρ c x₀ l lam B j)
def BoundBelow : Prop := ∀ (ρ : ℝ) (c x₀ C₀ l lam B j : ℕ), Numbers ρ c x₀ lam B → j < l →
  levelBound ρ c x₀ C₀ l lam B j ≤
    (2 : ℝ) ^ (Levels.Gen.e ρ x₀ (j + 1) * (Levels.Gen.K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1) - 3 * ((Levels.Gen.K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) / Levels.Gen.K x₀ j) *
      (xiAt ρ c x₀ l lam B j : ℝ) ^ (c * (Levels.Gen.g x₀ j ^ 4 / 4) + Levels.Gen.K x₀ j ^ 2 + (c + 5) * C₀ * Levels.Gen.K x₀ j ^ 2)
def BoundBelowFrom : Prop := ChainLabel → ChainBase → ChainExponent → BoundBelow
def CountBase : Prop := ∀ (C : ℕ) (ρ : ℝ) (c x₀ C₀ l lam B t : ℕ), Numbers ρ c x₀ lam B → 1 ≤ C₀ → 1 ≤ t →
  (solverCost C ρ c x₀ l lam B 0 0 t : ℝ) ≤ t * levelBound ρ c x₀ C₀ l lam B 0
def CountStep : Prop := ∀ c C : ℕ, ∃ C₄ : ℕ, ∀ (ρ : ℝ) (x₀ C₀ l lam B j t : ℕ), Numbers ρ c x₀ lam B → j < l → 1 ≤ t →
  (solverOwn C ρ c x₀ l lam B (j + 1) : ℝ) + solverCalls ρ c x₀ l lam B (j + 1) * (((entryCost C ρ c x₀ l lam B j t : ℕ) + 2) * levelBound ρ c x₀ C₀ l lam B j + 2) ≤
    t * ((2 : ℝ) ^ (Levels.Gen.e ρ x₀ (j + 1) * (Levels.Gen.K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) *
      (xiAt ρ c x₀ l lam B j : ℝ) ^ (c * Levels.Gen.g x₀ j ^ 4 / 2 + Levels.Gen.g x₀ j + Levels.Gen.K x₀ j ^ 2 + C₄ + (c + 5) * C₀ * Levels.Gen.K x₀ j ^ 2))
def ExponentFits : Prop := ∀ c C₄ C₀ x₀ j : ℕ, 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → 2 * (c + C₄ + 1) ≤ C₀ →
  c * Levels.Gen.g x₀ j ^ 4 / 2 + Levels.Gen.g x₀ j + Levels.Gen.K x₀ j ^ 2 + C₄ + (c + 5) * C₀ * Levels.Gen.K x₀ j ^ 2 ≤ C₀ * Levels.Gen.K x₀ (j + 1) ^ 2
def CountBaseFrom : Prop := ChainLabel → CountBase
def CountStepFrom : Prop := ChainLabel → BoundBelow → Levels.Gen.PartA → CountStep
def TotalCount : Prop := ∀ c C : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ l lam B : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 1 ≤ c → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → 1 ≤ lam → 1 ≤ B →
  (Tower.cost (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) l 1 : ℝ) ≤ timeBound ρ x₀ C₀ l lam B
def TotalCountFrom : Prop := CountBase → CountStep → ExponentFits → Tower.CostShape → TotalCount
def TotalRoom : Prop := ∀ c C : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ l lam B : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 1 ≤ c → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → 1 ≤ lam → 1 ≤ B →
  (Tower.towerSize l (roomAll C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B) : ℝ) ≤ sizeBound x₀ C₀ l lam B
def TotalRoomFrom : Prop := ChainBase → ChainLevels → TotalRoom
def RoomIsWithinTheBound : Prop := ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ l lam B : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 1 ≤ c → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → 1 ≤ lam → 1 ≤ B →
  (PiecesCounted.room c (lamMax ρ c x₀ l lam B) : ℝ) ≤ timeBound ρ x₀ C₀ l lam B
def RoomIsWithinTheBoundFrom : Prop := ChainLabel → BoundBelow → ChainLevels → ExponentFits → Levels.Gen.PartA → RoomIsWithinTheBound
def RecursionPoly : Prop := ∀ c x₀ : ℕ, (solver c x₀).PolyTimeSteps ∧ (procedure c).PolyTimeSteps
def RecursionPolyFrom : Prop := Tower.TowerPoly → RecursionPoly → ∀ c x₀ : ℕ, (recursion c x₀).PolyTimeSteps
def RecursionCountedUpTo : Prop := ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (l lam B : ℕ) (W : ℕ → List Bool → ℤ), 1 ≤ lam → 1 ≤ B →
  (∀ w < Levels.Gen.K x₀ l, ∀ z ∈ words ((Levels.Gen.K x₀ l - 1) * lam), |W w z| < 2 ^ B) →
    ∃ T S : ℕ, (recursion c x₀).Within (Sum.elim (answersOf (Levels.Gen.K x₀ l) lam W) (piecesUpTo D (lamMax ρ c x₀ l lam B))) (upPrices c 1) (top l lam B) T S (.inl (clique (Levels.Gen.K x₀ l) lam fun w => W w.val).value) ∧
      (T : ℝ) ≤ timeBound ρ x₀ C₀ l lam B ∧ (S : ℝ) ≤ sizeBound x₀ C₀ l lam B
def RecursionCountedUpToFrom : Prop := RecursionMeets → TotalCount → TotalRoom → Tower.TowerRuns → RecursionCountedUpTo
def RecursionPlugged : Prop := ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data) (Alg : Stepped PieceQuery Ans), PiecesCounted.IsPieces ρ c D Alg → Setting ρ c x₀ D → ∀ (l lam B : ℕ) (W : ℕ → List Bool → ℤ), 1 ≤ lam → 1 ≤ B →
  (∀ w < Levels.Gen.K x₀ l, ∀ z ∈ words ((Levels.Gen.K x₀ l - 1) * lam), |W w z| < 2 ^ B) →
    ∃ T S : ℕ, (recursionWith c x₀ Alg).Within (answersOf (Levels.Gen.K x₀ l) lam W) (fun _ => 1) (top l lam B) T S (.inl (clique (Levels.Gen.K x₀ l) lam fun w => W w.val).value) ∧
      (T : ℝ) ≤ 3 * timeBound ρ x₀ C₀ l lam B ∧ (S : ℝ) ≤ 2 * sizeBound x₀ C₀ l lam B + PiecesCounted.room c (lamMax ρ c x₀ l lam B)
def RecursionPluggedFrom : Prop := RecursionCountedUpTo → PricesScale → PiecesCounted.OracleFromAlgorithm → RecursionPlugged
def RecursionWithPoly : Prop := ∀ (c x₀ : ℕ) (Alg : Stepped PieceQuery Ans), Nonempty (IsPolyT Alg) → (recursionWith c x₀ Alg).PolyTimeSteps ∧ (cliqueMachine c x₀ Alg).PolyTimeSteps
def RecursionWithPolyFrom : Prop := (∀ c x₀ : ℕ, (recursion c x₀).PolyTimeSteps) → RecursionWithPoly
def RecursionSolves : Prop := ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data) (Alg : Stepped PieceQuery Ans), PiecesCounted.IsPieces ρ c D Alg → Setting ρ c x₀ D →
  (cliqueMachine c x₀ Alg).PolyTimeSteps ∧ CliqueLevels.Solves (cliqueMachine c x₀ Alg) (Levels.Gen.K x₀) (Levels.Gen.e ρ x₀) C₀
def RecursionSolvesFrom : Prop := RecursionPlugged → RoomIsWithinTheBound → ReadAsRuns → RecursionWithPoly → RecursionSolves
end ExplicitCost


