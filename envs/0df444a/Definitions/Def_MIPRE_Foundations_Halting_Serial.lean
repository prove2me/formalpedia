-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Serial
-- name    : MIPRE_Foundations_Halting_Serial
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:50:46.872155+00:00
-- url     : https://prove2.me/theorems/80334891-fa3a-49cc-a526-19f6bdf7610e
-- title:
--   Parsing and serializing descriptions inside the ambient model
-- statement:
--   Descriptions of verifiers are bit strings: the postorder serialization `Data.toBitsPost` of a datum ($\mathtt{nil} \mapsto 0$, $\mathtt{cons}\,a\,b \mapsto a\,b\,1$), read back by the stack machine `Data.parse`. This bundle gives the two programs of the ambient model that move between a datum and its serialization, with the serializer's cost; the compressor reads descriptions with the first and writes its output with the second.
--
--   **Parsing.** `MIPRE.Cost.Prog.parseBody` is the body of a loop on the state $\mathtt{cons}\ \mathit{bits}\ \mathit{stack}$: at the end of the bits it stops with the top of the stack ($\mathtt{nil}$ if empty); on a $0$ it pushes $\mathtt{nil}$; on a $1$ it pops two entries and pushes their pair, leaving a stack with fewer than two entries alone. `parseProg = let_ (cons (var 0) nil) (loop parseBody)` computes `parse x` on an encoded bit string $x$.
--
--   **Serializing.** The serializer works on a list of pending items, a datum still to be written or a marker for the closing $1$ of a pair. `MIPRE.Cost.Data.itemD` encodes an item (`some d` as $\mathtt{cons}\ \mathtt{nil}\ d$, `none` as $\mathtt{nil}$); `serItems` is the bit string the pending items still produce; `serMeasure` (on lists of items) and `serMeasureD` (on their data) count $3\,\mathrm{size}(d) + 1$ per datum and $1$ per marker. `Prog.serBody` is the loop body on the state $\mathtt{cons}\ \mathit{pending}\ \mathit{acc}$: at the end it stops with $\mathit{acc}$; a marker writes a $1$; the datum $\mathtt{nil}$ writes a $0$; a pair $\mathtt{cons}\ a\ b$ schedules $a$, $b$ and a marker. `serProg` starts the loop on the single item $d$ with an empty accumulator and reverses the result with `revProg`.
--
--   The embedded lemmas are the well-scopedness of `serBody` and `serProg`, one step lemma per case of `serBody` with its cost, the loop invariant `serLoop_runs` and the run of the whole program:
--   $$\exists\, t \le (3\,\mathrm{size}(d) + 2)(16\,\mathrm{size}(d) + 42) + (\mathrm{size}(d) + 2)(5\,\mathrm{size}(d) + 30),\quad \mathrm{serProg}.\mathrm{Runs}\; d\; (\mathrm{encode}\; d.\mathrm{toBitsPost})\; t .$$
--
--   **Formalization Note**. `parseBody` and `serBody` are literal terms of the ambient language with de Bruijn indices. The docstring of `parseProg` states what it computes, but no run lemma for the parser is among this bundle's declarations; `serProg_runs` is the only statement about `serProg`, with an explicit, not tight cost bound.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Serial.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Serial.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists

/-!
# Reading and writing descriptions, in the ambient model

The two programs that move between a datum and its postorder serialization
(`Data.toBitsPost`, `Halting/Descriptions.lean`):

* `Prog.parseProg`: the stack machine `Data.stackRun` on a bit string, returning the top of the
  final stack (`Data.parse`). The compressor's decider reads the description it was handed with
  it (`Halting/Compressor.lean`).
* `Prog.serProg`: the postorder serialization of a datum, by a loop over a list of pending
  items — a datum still to be written, or a marker for the closing `1` of a pair — accumulating
  the bits in reverse and reversing at the end. The compressor writes its output with it.

Both run in time quadratic in the size of their input: each step copies the remainder of the
work list and the accumulator.
-/

namespace MIPRE.Cost

namespace Data

/-- A pending item of the serializer: a datum to write (`some d`, as `cons nil d`) or the
closing `1` of a pair (`none`, as `nil`). -/
def itemD : Option Data → Data
  | some d => cons nil d
  | none => nil

/-- The bits still to be written for a list of pending items. -/
def serItems : List (Option Data) → BitStr
  | [] => []
  | some d :: r => d.toBitsPost ++ serItems r
  | none :: r => true :: serItems r

/-- The measure of a list of pending items, decreasing along the serializer's loop. -/
def serMeasure : List (Option Data) → ℕ
  | [] => 0
  | some d :: r => 3 * d.size + 1 + serMeasure r
  | none :: r => 1 + serMeasure r

/-- The same measure, on the data of the pending list (for the loop invariant). -/
def serMeasureD : Data → ℕ
  | nil => 0
  | cons nil r => 1 + serMeasureD r
  | cons (cons _ d) r => 3 * d.size + 1 + serMeasureD r

end Data

namespace Prog

open Data

/-! ## The parser -/

/-- Body of `parseProg`, on the state `cons bits stack`: at the end, stop with the top of the
stack (`nil` if empty); on a `0`, push `nil`; on a `1`, pop two entries and push their pair,
leaving a stack with fewer than two entries alone. -/
def parseBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.elim 1 .nil (.var 0)))
      (.elim 0 (.cons (.cons .nil .nil) (.cons (.var 1) (.cons .nil (.var 3))))
        (.elim 5 (.cons (.cons .nil .nil) (.cons (.var 3) (.var 5)))
          (.elim 1 (.cons (.cons .nil .nil) (.cons (.var 5) (.var 7)))
            (.cons (.cons .nil .nil)
              (.cons (.var 7) (.cons (.cons (.var 0) (.var 2)) (.var 1))))))))

/-- `parseProg` on an encoded bit string `x` computes `parse x`. -/
def parseProg : Prog := .let_ (.cons (.var 0) .nil) (.loop parseBody)

/-! ## The serializer -/

/-- Body of `serProg`, on the state `cons pending acc`: at the end, stop with `acc`; a marker
writes a `1`; the datum `nil` writes a `0`; a pair `cons a b` schedules `a`, `b` and a marker. -/
def serBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.elim 0 (.cons (.cons .nil .nil) (.cons (.var 1) (.cons (.cons .nil .nil) (.var 3))))
        (.elim 1 (.cons (.cons .nil .nil) (.cons (.var 3) (.cons .nil (.var 5))))
          (.cons (.cons .nil .nil)
            (.cons (.cons (.cons .nil (.var 0)) (.cons (.cons .nil (.var 1)) (.cons .nil (.var 5))))
              (.var 7))))))

/-- `serProg` on `d` computes `encode d.toBitsPost`. -/
def serProg : Prog :=
  .let_ (.cons (.cons (.cons .nil (.var 0)) .nil) .nil) (.let_ (.loop serBody) revProg)

theorem serBody_wellScoped : serBody.WellScoped 1 := by simp [serBody, WellScoped]

theorem serProg_wellScoped : serProg.WellScoped 1 := by
  simp [serProg, WellScoped, serBody, revProg, revOntoProg, revOntoBody]

theorem serBody_stop (acc : BitStr) :
    ∃ t ≤ (encode acc : Data).size + 20,
      Eval [Data.cons (list ([] : List Data)) (encode acc)] serBody (Data.cons Data.nil (encode acc)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := list ([] : List Data)) (b := encode acc) (by simp)
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := encode acc) (by simp))))⟩
  ((try simp only [MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)

theorem serBody_marker (rest : List Data) (acc : BitStr) :
    ∃ t ≤ (list rest).size + (encode acc : Data).size + 20,
      Eval [Data.cons (list (Data.nil :: rest)) (encode acc)] serBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (list rest) (encode (true :: acc)))) t := by
  simp only [encode_bitStr_cons, ofBool, list_cons]
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := list (Data.nil :: rest)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := list rest) (by simp)
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 1) (v := list rest) (by simp)) (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.var_of_get (i := 3) (v := encode acc) (by simp)))))))⟩
  ((try simp only [MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)

theorem serBody_datanil (rest : List Data) (acc : BitStr) :
    ∃ t ≤ (list rest).size + (encode acc : Data).size + 20,
      Eval [Data.cons (list (Data.cons Data.nil Data.nil :: rest)) (encode acc)] serBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (list rest) (encode (false :: acc)))) t := by
  simp only [encode_bitStr_cons, ofBool, list_cons]
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := list (Data.cons Data.nil Data.nil :: rest)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.cons Data.nil Data.nil) (b := list rest) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
    (Eval.elim_nil (i := 1) (by simp)
    (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 3) (v := list rest) (by simp)) (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := encode acc) (by simp))))))))⟩
  ((try simp only [MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)

theorem serBody_datacons (a b : Data) (rest : List Data) (acc : BitStr) :
    ∃ t ≤ a.size + b.size + (list rest).size + (encode acc : Data).size + 30,
      Eval [Data.cons (list (Data.cons Data.nil (Data.cons a b) :: rest)) (encode acc)] serBody
        (Data.cons (Data.cons Data.nil Data.nil)
          (Data.cons (list (Data.cons Data.nil a :: Data.cons Data.nil b :: Data.nil :: rest))
            (encode acc))) t := by
  simp only [list_cons]
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := list (Data.cons Data.nil (Data.cons a b) :: rest)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.cons Data.nil (Data.cons a b)) (b := list rest) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.cons a b) (by simp)
    (Eval.elim_cons (i := 1) (a := a) (b := b) (by simp)
    (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := a) (by simp))) (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := b) (by simp))) (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := list rest) (by simp))))) (Eval.var_of_get (i := 7) (v := encode acc) (by simp)))))))⟩
  ((try simp only [MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)

/-- The serializer's loop, by the invariant "`acc.reverse ++ serItems items` is the target",
with the measure `serMeasure` and the size bound `S₀`. -/
theorem serLoop_runs (d : Data) (env : Env) :
    ∃ t ≤ (3 * d.size + 2) * (16 * d.size + 42),
      Eval (Data.cons (list [itemD (some d)]) (encode ([] : BitStr)) :: env) (.loop serBody)
        (encode d.toBitsPost.reverse) t := by
  set S₀ := d.size + 6 + 5 * (3 * d.size + 1) with hS₀
  -- the invariant
  let I : Data → Prop := fun st => ∃ (items : List (Option Data)) (acc : BitStr),
    st = Data.cons (list (items.map itemD)) (encode acc) ∧
    acc.reverse ++ serItems items = d.toBitsPost ∧ st.size + 5 * serMeasure items ≤ S₀
  let μ : Data → ℕ := fun st => serMeasureD st.left
  have key := Eval.loop_of_invariant serBody_wellScoped env I μ
    (fun r => r = encode d.toBitsPost.reverse) (S₀ + 30) ?_
    (Data.cons (list [itemD (some d)]) (encode ([] : BitStr))) ?_
  · obtain ⟨r, t, ht, hr, hrun⟩ := key
    subst hr
    refine ⟨t, ?_, hrun⟩
    refine ht.trans ?_
    simp only [μ, Data.left_cons, list_cons, list_nil, itemD, serMeasureD, Data.size_nil, hS₀]
    nlinarith
  · -- the body
    rintro st ⟨items, acc, rfl, hacc, hsize⟩
    rcases items with _ | ⟨it, rest⟩
    · -- done
      left
      obtain ⟨t, ht, hrun⟩ := serBody_stop acc
      refine ⟨encode acc, t, ?_, hrun, ?_⟩
      · simp only [List.map_nil, list_nil, Data.size_cons, Data.size_nil] at hsize ⊢; omega
      · simp only [serItems, List.append_nil] at hacc
        rw [← hacc, List.reverse_reverse]
    · right
      rcases it with _ | d'
      · -- marker
        obtain ⟨t, ht, hrun⟩ := serBody_marker (rest.map itemD) acc
        refine ⟨_, _, _, t, ?_, hrun, ⟨rest, true :: acc, rfl, ?_, ?_⟩, ?_⟩
        · simp only [List.map_cons, itemD, list_cons, Data.size_cons, Data.size_nil] at hsize; omega
        · simpa [serItems, List.reverse_cons] using hacc
        · simp only [List.map_cons, itemD, list_cons, Data.size_cons, Data.size_nil, serMeasure,
            encode_bitStr_cons, ofBool] at hsize ⊢
          omega
        · simp [μ, List.map_cons, itemD, serMeasureD]
      · rcases d' with _ | ⟨a, b⟩
        · -- the datum `nil`
          obtain ⟨t, ht, hrun⟩ := serBody_datanil (rest.map itemD) acc
          refine ⟨_, _, _, t, ?_, by simpa [itemD] using hrun, ⟨rest, false :: acc, rfl, ?_, ?_⟩, ?_⟩
          · simp only [List.map_cons, itemD, list_cons, Data.size_cons, Data.size_nil] at hsize; omega
          · simpa [serItems, toBitsPost, List.reverse_cons] using hacc
          · simp only [List.map_cons, itemD, list_cons, Data.size_cons, Data.size_nil, serMeasure,
              encode_bitStr_cons, ofBool] at hsize ⊢
            omega
          · simp [μ, List.map_cons, itemD, serMeasureD]
        · -- a pair
          obtain ⟨t, ht, hrun⟩ := serBody_datacons a b (rest.map itemD) acc
          refine ⟨_, _, _, t, ?_, by simpa [itemD] using hrun,
            ⟨some a :: some b :: none :: rest, acc, by simp [itemD], ?_, ?_⟩, ?_⟩
          · simp only [List.map_cons, itemD, list_cons, Data.size_cons, Data.size_nil] at hsize; omega
          · simpa [serItems, toBitsPost, List.append_assoc] using hacc
          · simp only [List.map_cons, itemD, list_cons, Data.size_cons, Data.size_nil, serMeasure]
              at hsize ⊢
            omega
          · simp [μ, List.map_cons, itemD, serMeasureD]; omega
  · -- the initial state
    refine ⟨[some d], [], rfl, by simp [serItems], ?_⟩
    simp only [List.map_cons, List.map_nil, itemD, list_cons, list_nil, Data.size_cons, Data.size_nil,
      serMeasure, encode_bitStr_nil, hS₀]
    omega

/-- `serProg` writes the postorder serialization. -/
theorem serProg_runs (d : Data) :
    ∃ t ≤ (3 * d.size + 2) * (16 * d.size + 42) + (d.size + 2) * (5 * d.size + 30),
      serProg.Runs d (encode d.toBitsPost) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := serLoop_runs d [d]
  have hpre := Eval.cons (Eval.cons (Eval.cons (Eval.nil [d])
    (Eval.var_of_get (env := [d]) (i := 0) (v := d) (by simp))) (Eval.nil [d])) (Eval.nil [d])
  obtain ⟨t₂, ht₂, h₂⟩ := revProg_runs (d.toBitsPost.reverse.map ofBool)
  have h₂' : Eval [encode d.toBitsPost.reverse,
      Data.cons (Data.cons (Data.cons Data.nil d) Data.nil) Data.nil, d] revProg
      (encode d.toBitsPost) t₂ := by
    have := Eval.append_of_wellScoped h₂ revProg_wellScoped
      [Data.cons (Data.cons (Data.cons Data.nil d) Data.nil) Data.nil, d]
    rw [encode_bitStr_eq_list, encode_bitStr_eq_list]
    simpa [List.map_reverse] using this
  have h₁' : Eval [Data.cons (Data.cons (Data.cons Data.nil d) Data.nil) Data.nil, d] (.loop serBody)
      (encode d.toBitsPost.reverse) t₁ := by
    simpa [itemD, encode_bitStr_nil] using h₁
  refine ⟨_, ?_, Eval.let_ hpre (Eval.let_ h₁' h₂')⟩
  have hlen : d.toBitsPost.reverse.length = d.size := by simp
  have hsz : (encode d.toBitsPost.reverse : Data).size ≤ 4 * d.size + 1 := by
    have := esize_bitStr_le d.toBitsPost.reverse
    rw [hlen] at this; exact this
  have hB : t₂ ≤ (d.size + 2) * (4 * d.size + 14) := by
    refine ht₂.trans ?_
    rw [← encode_bitStr_eq_list, List.length_map, hlen]
    exact Nat.mul_le_mul_left _ (by omega)
  nlinarith
end Prog

end MIPRE.Cost


