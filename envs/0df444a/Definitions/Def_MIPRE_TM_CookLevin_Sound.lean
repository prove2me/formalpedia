-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Sound
-- name    : MIPRE_TM_CookLevin_Sound
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:56:11.729045+00:00
-- url     : https://prove2.me/theorems/215e9384-0dfc-4cda-87b2-1e5ad9d3611b
-- title:
--   Definitions of Sound: Soundness of the Cook–Levin tableau A satisfying assignment of the tableau formula comes from an accepting run…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Sound` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of the Cook–Levin tableau. A satisfying assignment of the tableau formula comes from an accepting run (`acceptsIn_of_tableau_sat`), and the equivalence `tableau_sat_iff` (`planning/succinct-cook-levin.md`, S1). * The successor part of a locally consistent window is a function of its time-`t` part (`post_of_pre`): two locally consistent local configurations with the same cells, heads and state at time `t`, one of them with at most one head per tape, agree on the cell and head at time `t + 1` of every tape whose head is far, and on everything when every head is in the window. * The…
--
--   **Definitions** (9): `MIPRE.TM.CookLevin.FreeFacts` (What the free-tape clauses say about tape `j` at time `0`.); `MIPRE.TM.CookLevin.RowOk` (Row `t` of the assignment `a` encodes the configuration `c`.); `MIPRE.TM.CookLevin.blankBit` (The blank bit of cell `k + 3` of input tape `j` at time `0` (`true` past the last cell).); `MIPRE.TM.CookLevin.cellCenter` (The centers putting the cell `p` of tape `d` at the middle of its window and the head of every other tape at offset `2`.); `MIPRE.TM.CookLevin.freeLen` (The length of the string on a free tape: the first cell, from cell `3`, that is blank or a boundary cell.); `MIPRE.TM.CookLevin.freeString` (The string on free tape `j`, read off row `0`: `s₀` where the `s₀` bit is set, else `s₁`, up to the first blank.); `MIPRE.TM.CookLevin.headCenter` (The center putting the head of `d` at offset `2`.); `MIPRE.TM.CookLevin.inputOf` (The inputs read off a satisfying assignment: the fixed strings, and on the free tapes the strings on the time-`0` rows.); `MIPRE.TM.CookLevin.symBit` (The `s` bit of cell `k + 3` of input tape `j` at time `0`.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `freeLen_exists`, `headCell_sub_two_toNat`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Sound` (`MIPRE/TM/CookLevin/Sound.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 12 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Sound.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sound.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Theorems.Thm_MIPRE_TM_CookLevin_HeadsIn_headCell_bounds
import Theorems.Thm_MIPRE_TM_CookLevin_not_isBdry_iff

/-!
# Soundness of the Cook–Levin tableau

A satisfying assignment of the tableau formula comes from an accepting run
(`acceptsIn_of_tableau_sat`), and the equivalence `tableau_sat_iff`
(`planning/succinct-cook-levin.md`, S1).

* The successor part of a locally consistent window is a function of its time-`t` part
  (`post_of_pre`): two locally consistent local configurations with the same cells, heads
  and state at time `t`, one of them with at most one head per tape, agree on the cell and
  head at time `t + 1` of every tape whose head is far, and on everything when every head is
  in the window.
* The free input strings are read off the time-`0` rows (`freeString`): the symbols from
  cell `3` up to the first blank, which the free-tape clauses make well defined
  (`FreeFacts.cell_eq`).
* The rows encode the run (`rows_of_sat`), by induction on time: the window centered at a
  cell, with the other windows centered at the heads, determines the cell and head at the
  next time; the window centered at every head determines the state and the emission bits.
-/

namespace MIPRE.TM.CookLevin

open Turing SAT MultiInputTM

/-! ## The successor part of a window is determined -/

section Post

variable {i w : ℕ} {Symbol State : Type*} [DecidableEq Symbol] [DecidableEq State]
  (M : MultiInputTM i w Symbol State) (acc : Symbol)

end Post

/-! ## The free input strings -/

section Extract

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}

/-- The blank bit of cell `k + 3` of input tape `j` at time `0` (`true` past the last cell). -/
def blankBit (a : TabVar i w Symbol State S G → Bool) (j : Fin i) (k : ℕ) : Bool :=
  if h : k + 3 < numCells S then a (.cell 0 (.inl j) ⟨k + 3, h⟩ .blank) else true

/-- The `s` bit of cell `k + 3` of input tape `j` at time `0`. -/
def symBit (a : TabVar i w Symbol State S G → Bool) (j : Fin i) (s : Symbol) (k : ℕ) : Bool :=
  if h : k + 3 < numCells S then a (.cell 0 (.inl j) ⟨k + 3, h⟩ (.sym s)) else false

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem freeLen_exists (a : TabVar i w Symbol State S G → Bool) (j : Fin i) :
    ∃ k, blankBit a j k = true ∨ numCells S ≤ k + 5 :=
  ⟨numCells S, Or.inr (by omega)⟩

/-- The length of the string on a free tape: the first cell, from cell `3`, that is blank
or a boundary cell. -/
noncomputable def freeLen (a : TabVar i w Symbol State S G → Bool) (j : Fin i) : ℕ :=
  Nat.find (freeLen_exists a j)

/-- The string on free tape `j`, read off row `0`: `s₀` where the `s₀` bit is set, else
`s₁`, up to the first blank. -/
noncomputable def freeString (a : TabVar i w Symbol State S G → Bool) (j : Fin i)
    (s₀ s₁ : Symbol) : List Symbol :=
  List.ofFn fun k : Fin (freeLen a j) => if symBit a j s₀ k then s₀ else s₁

variable (s₀ s₁ : Symbol)

/-- What the free-tape clauses say about tape `j` at time `0`. -/
structure FreeFacts (a : TabVar i w Symbol State S G → Bool) (j : Fin i) : Prop where
  bdry : ∀ (p : Pos S) v, p.IsBdry → a (.cell 0 (.inl j) p v) = decide (v = .bdry)
  other : ∀ (p : Pos S) v, ¬ p.IsBdry → v ≠ .sym s₀ → v ≠ .sym s₁ → v ≠ .blank →
    a (.cell 0 (.inl j) p v) = false
  two : ∀ v, a (.cell 0 (.inl j) ⟨2, by unfold numCells; omega⟩ v) = decide (v = .blank)
  some : ∀ p : Pos S, ¬ p.IsBdry → a (.cell 0 (.inl j) p (.sym s₀)) = true ∨
    a (.cell 0 (.inl j) p (.sym s₁)) = true ∨ a (.cell 0 (.inl j) p .blank) = true
  once : ∀ (p : Pos S) v v', ¬ p.IsBdry → v ≠ v' →
    ¬ (a (.cell 0 (.inl j) p v) = true ∧ a (.cell 0 (.inl j) p v') = true)
  mono : ∀ p p' : Pos S, 2 < (p : ℕ) → ¬ p'.IsBdry → p < p' →
    a (.cell 0 (.inl j) p .blank) = true → a (.cell 0 (.inl j) p' .blank) = true

variable {s₀ s₁}

end Extract

/-! ## The rows encode the run -/

section Rows

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}

/-- Row `t` of the assignment `a` encodes the configuration `c`. -/
structure RowOk (a : TabVar i w Symbol State S G → Bool) (t : Fin (S + 1))
    (c : Cfg i w Symbol State input) : Prop where
  cell : ∀ d p v, a (.cell t d p v) = decide (cellValAt (S := S) c d p = v)
  head : ∀ d p, a (.head t d p) = decide (headCell (S := S) c d = p)
  state : ∀ q, a (.state t q) = decide (c.state = q)

/-! ### Windows centered at the heads and at a cell -/

omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem headCell_sub_two_toNat (c : Cfg i w Symbol State input) (hin : HeadsIn c S) (d : Tape i w) :
    (((headCell (S := S) c d - 2).toNat : ℕ) : ℤ) = headCell (S := S) c d - 2 :=
  Int.toNat_of_nonneg (by have := hin.headCell_bounds d; omega)

/-- The center putting the head of `d` at offset `2`. -/
def headCenter (c : Cfg i w Symbol State input) (hin : HeadsIn c S) (d : Tape i w) : Center S :=
  ⟨(headCell (S := S) c d - 2).toNat, by
    have := hin.headCell_bounds d
    have h := headCell_sub_two_toNat c hin d
    have hnc : numCells S = 2 * S + 7 := rfl
    omega⟩

/-- The centers putting the cell `p` of tape `d` at the middle of its window and the head of
every other tape at offset `2`. -/
def cellCenter (c : Cfg i w Symbol State input) (hin : HeadsIn c S) (d : Tape i w) (p : Pos S)
    (hnb : ¬ p.IsBdry) : Tape i w → Center S :=
  fun d' => if d' = d then
    ⟨(p : ℕ) - 2, by
      rw [not_isBdry_iff] at hnb
      have hnc : numCells S = 2 * S + 7 := rfl
      omega⟩
  else headCenter c hin d'

/-! ### The step -/

end Rows

/-! ## From a satisfying assignment to an accepting run -/

section Sound

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
  (chk : Circuit) (a : TabVar i w Symbol State S chk.gates.length → Bool)

/-- The inputs read off a satisfying assignment: the fixed strings, and on the free tapes
the strings on the time-`0` rows. -/
noncomputable def inputOf : Fin i → List Symbol :=
  fun j => (fixed j).getD (freeString a j s₀ s₁)

variable (hSat : (tableau M s₀ s₁ S fixed chk).Sat a)
include hSat

end Sound

/-! ## The equivalence -/

section Iff

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
  (chk : Circuit)

end Iff

end MIPRE.TM.CookLevin


