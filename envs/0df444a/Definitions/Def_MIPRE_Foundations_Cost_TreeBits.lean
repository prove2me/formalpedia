-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_TreeBits
-- name    : MIPRE_Foundations_Cost_TreeBits
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:09:46.016046+00:00
-- url     : https://prove2.me/theorems/7d8896d8-3c21-46a8-b81a-0d182dc147d3
-- title:
--   Definitions of TreeBits: The closure library, part VI: the bits of a tree The preorder serialization `Data.toBits` of a tree, as a program…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Cost.TreeBits` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The closure library, part VI: the bits of a tree. The preorder serialization `Data.toBits` of a tree, as a program (`toBitsProg`, a stack-driven traversal after `sizeProg`) and as a polynomial-time function (`PolyTimeFun.toBits`). This is how the describer of the succinct Cook–Levin theorem obtains the symbol strings of the interpreter machine's fixed input tapes — `S d = bits d.toBits` — from the data `d` (`planning/succinct-cook-levin.md`, S3).
--
--   **Definitions** (7): `MIPRE.Cost.PolyTimeFun.toBits` (The bits of a tree, in polynomial time.); `MIPRE.Cost.Prog.tbCons` (The step on a `cons` subtree: emit `1` and push the children.); `MIPRE.Cost.Prog.tbNil` (The step on a `nil` subtree: emit `0`.); `MIPRE.Cost.Prog.tbStop` (Body of `toBitsProg`: the state is `cons stack acc`, `stack` a list of pending subtrees and `acc` the bits produced so far, reversed.); `MIPRE.Cost.Prog.toBitsBody` (The body of the serialization loop.); `MIPRE.Cost.Prog.toBitsInv` (The invariant of the serialization loop for the target bits `target`: the state is `cons stack acc` with `reverse acc ++ toBits stack₁ ++ ……); `MIPRE.Cost.Prog.toBitsProg` (The bits of a tree: `toBitsProg` on `d` computes `encode d.toBits`.).
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `toBits_apply`, `toBitsBody_step_cons`, `toBitsBody_step_nil`, `toBitsBody_stop`, `toBitsBody_wellScoped`, `toBitsLoop_runs`, `toBitsProg_runs`, `toBitsProg_wellScoped`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Cost.TreeBits` (`MIPRE/Foundations/Cost/TreeBits.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 9 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/TreeBits.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/TreeBits.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary

/-!
# The closure library, part VI: the bits of a tree

The preorder serialization `Data.toBits` of a tree, as a program (`toBitsProg`, a
stack-driven traversal after `sizeProg`) and as a polynomial-time function
(`PolyTimeFun.toBits`). This is how the describer of the succinct Cook–Levin theorem obtains
the symbol strings of the interpreter machine's fixed input tapes — `S d = bits d.toBits` —
from the data `d` (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.Cost

open Polynomial

namespace Prog

/-- Body of `toBitsProg`: the state is `cons stack acc`, `stack` a list of pending subtrees
and `acc` the bits produced so far, reversed. Pop a subtree: `nil` emits `0`; `cons a b` emits
`1` and pushes `a` then `b`. Stop with `acc` when the stack is empty. -/
def tbStop : Prog := .cons .nil (.var 1)

/-- The step on a `nil` subtree: emit `0`. -/
def tbNil : Prog := .cons (.cons .nil .nil) (.cons (.var 1) (.cons .nil (.var 3)))

/-- The step on a `cons` subtree: emit `1` and push the children. -/
def tbCons : Prog :=
  .cons (.cons .nil .nil)
    (.cons (.cons (.var 0) (.cons (.var 1) (.var 3))) (.cons (.const (.cons .nil .nil)) (.var 5)))

/-- The body of the serialization loop. -/
def toBitsBody : Prog := .elim 0 .nil (.elim 0 tbStop (.elim 0 tbNil tbCons))

theorem toBitsBody_wellScoped : toBitsBody.WellScoped 1 := by
  simp [toBitsBody, tbStop, tbNil, tbCons, WellScoped]

theorem toBitsBody_stop (acc : BitStr) :
    Eval [.cons (.list []) (encode acc)] toBitsBody (.cons .nil (encode acc)) (esize acc + 5) := by
  have e := Eval.elim_cons (env := [Data.cons (.list []) (encode acc)]) (i := 0)
    (n := .nil) (a := .list []) (b := encode acc) (by simp)
    (Eval.elim_nil (i := 0) (c := .elim 0 tbNil tbCons) (by simp)
      (show Eval _ tbStop _ _ from
        Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := encode acc) (by simp))))
  exact e.cast_cost (by simp only [esize]; omega)

theorem toBitsBody_step_nil (rest : List Data) (acc : BitStr) :
    Eval [.cons (.list (.nil :: rest)) (encode acc)] toBitsBody
      (.cons (.cons .nil .nil) (.cons (.list rest) (encode (false :: acc))))
      ((Data.list rest).size + esize acc + 12) := by
  have e := Eval.elim_cons (env := [Data.cons (.list (.nil :: rest)) (encode acc)]) (i := 0)
    (n := .nil) (a := .list (.nil :: rest)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (n := tbStop) (a := .nil) (b := .list rest) (by simp)
      (Eval.elim_nil (i := 0) (c := tbCons) (by simp)
        (show Eval _ tbNil _ _ from
          Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 1) (v := .list rest) (by simp))
              (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 3) (v := encode acc) (by simp)))))))
  exact e.cast_cost (by simp only [esize]; omega)

theorem toBitsBody_step_cons (a b : Data) (rest : List Data) (acc : BitStr) :
    Eval [.cons (.list (.cons a b :: rest)) (encode acc)] toBitsBody
      (.cons (.cons .nil .nil) (.cons (.list (a :: b :: rest)) (encode (true :: acc))))
      (a.size + b.size + (Data.list rest).size + esize acc + 18) := by
  have e := Eval.elim_cons (env := [Data.cons (.list (.cons a b :: rest)) (encode acc)]) (i := 0)
    (n := .nil) (a := .list (.cons a b :: rest)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (n := tbStop) (a := .cons a b) (b := .list rest) (by simp)
      (Eval.elim_cons (i := 0) (n := tbNil) (a := a) (b := b) (by simp)
        (show Eval _ tbCons _ _ from
          Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons
              (Eval.cons (Eval.var_of_get (i := 0) (v := a) (by simp))
                (Eval.cons (Eval.var_of_get (i := 1) (v := b) (by simp))
                  (Eval.var_of_get (i := 3) (v := .list rest) (by simp))))
              (Eval.cons (Eval.const _ (.cons .nil .nil))
                (Eval.var_of_get (i := 5) (v := encode acc) (by simp)))))))
  exact e.cast_cost (by simp only [esize, Data.size_cons, Data.size_nil]; omega)

/-- The invariant of the serialization loop for the target bits `target`: the state is
`cons stack acc` with `reverse acc ++ toBits stack₁ ++ … = target`. -/
def toBitsInv (target : BitStr) (s : Data) : Prop :=
  ∃ (st : List Data) (acc : BitStr), s = .cons (.list st) (encode acc) ∧
    acc.reverse ++ (st.map Data.toBits).flatten = target

theorem toBitsLoop_runs (d : Data) (env : Env) (s : Data) (hs : toBitsInv d.toBits s) :
    ∃ t ≤ (Data.stackMeasure s + 1) * (8 * d.size + 21),
      ∃ acc : BitStr, acc.reverse = d.toBits ∧ Eval (s :: env) (.loop toBitsBody) (encode acc) t := by
  have key := Eval.loop_of_invariant toBitsBody_wellScoped env (toBitsInv d.toBits) Data.stackMeasure
    (fun r => ∃ acc : BitStr, acc.reverse = d.toBits ∧ r = encode acc) (8 * d.size + 20) ?_ s hs
  · obtain ⟨r, t, ht, ⟨acc, hacc, rfl⟩, hrun⟩ := key
    exact ⟨t, ht, acc, hacc, hrun⟩
  · rintro s ⟨st, acc, rfl, hk⟩
    -- the length bookkeeping
    have hlen : acc.length + Data.sumSize st = d.size := by
      have := congrArg List.length hk
      simp only [List.length_append, List.length_reverse, List.length_flatten, List.map_map,
        Data.length_toBits] at this
      rw [← this]
      congr 1
      clear hk this
      induction st with
      | nil => rfl
      | cons t st ih => simp [Data.sumSize_cons, ih, Data.length_toBits, List.sum_cons]
    have hacc : esize acc ≤ 4 * acc.length + 1 := esize_bitStr_le acc
    have hsz : (Data.list st).size = Data.sumSize st + st.length + 1 := Data.size_list_eq st
    have hst := Data.length_le_sumSize st
    rcases st with _ | ⟨t, rest⟩
    · left
      refine ⟨encode acc, esize acc + 5, ?_, toBitsBody_stop acc, acc, ?_, rfl⟩
      · simp only [Data.sumSize_nil, List.length_nil] at hlen; omega
      · simpa using hk
    · right
      simp only [Data.sumSize_cons] at hlen
      have hsz' : (Data.list rest).size = Data.sumSize rest + rest.length + 1 := Data.size_list_eq rest
      have hrest := Data.length_le_sumSize rest
      rcases t with _ | ⟨a, b⟩
      · refine ⟨.nil, .nil, _, _, ?_, toBitsBody_step_nil rest acc, ⟨rest, false :: acc, rfl, ?_⟩, ?_⟩
        · simp only [Data.size_nil] at hlen; omega
        · simpa [Data.toBits] using hk
        · simp only [Data.stackMeasure, Data.nodeSum_list, Data.sumSize_cons, Data.size_nil]; omega
      · refine ⟨.nil, .nil, _, _, ?_, toBitsBody_step_cons a b rest acc,
          ⟨a :: b :: rest, true :: acc, rfl, ?_⟩, ?_⟩
        · simp only [Data.size_cons] at hlen; omega
        · simpa [Data.toBits] using hk
        · simp only [Data.stackMeasure, Data.nodeSum_list, Data.sumSize_cons, Data.size_cons]; omega

/-- The bits of a tree: `toBitsProg` on `d` computes `encode d.toBits`. -/
def toBitsProg : Prog :=
  .let_ (.cons (.cons (.var 0) .nil) .nil) (.let_ (.loop toBitsBody) revProg)

theorem toBitsProg_wellScoped : toBitsProg.WellScoped 1 :=
  ⟨⟨⟨Nat.zero_lt_one, trivial⟩, trivial⟩,
    ⟨⟨Nat.zero_lt_succ 1, toBitsBody_wellScoped.mono (by omega) _⟩, revProg_wellScoped.mono (by omega) _⟩⟩

theorem toBitsProg_runs (d : Data) :
    ∃ t ≤ (d.size + 2) * (13 * d.size + 41), toBitsProg.Runs d (encode d.toBits) t := by
  obtain ⟨t₁, ht₁, acc, hacc, h₁⟩ := toBitsLoop_runs d [d] (.cons (.list [d]) (encode ([] : BitStr)))
    ⟨[d], [], rfl, by simp⟩
  have hlen : acc.length = d.size := by rw [← List.length_reverse, hacc, Data.length_toBits]
  obtain ⟨t₂, ht₂, h₂⟩ := revProg_runs (acc.map Data.ofBool)
  have hsz : (Data.list (acc.map Data.ofBool)).size ≤ 4 * d.size + 1 := by
    rw [← encode_bitStr_eq_list, ← hlen]; exact esize_bitStr_le acc
  refine ⟨d.size + 1 + 1 + 1 + 1 + 1 + (t₁ + t₂ + 1) + 1, ?_, ?_⟩
  · simp only [Data.stackMeasure, Data.nodeSum_list, Data.sumSize_cons, Data.sumSize_nil,
      Nat.add_zero] at ht₁
    simp only [List.length_map, hlen] at ht₂
    have hA : t₂ ≤ (d.size + 2) * (4 * d.size + 14) :=
      ht₂.trans (Nat.mul_le_mul_left _ (by omega))
    have hB : t₁ ≤ (d.size + 1) * (8 * d.size + 21) := ht₁
    have hC : (d.size + 1) * (8 * d.size + 21) ≤ (d.size + 2) * (8 * d.size + 21) :=
      Nat.mul_le_mul_right _ (by omega)
    have hD : (d.size + 2) * (4 * d.size + 14) + (d.size + 2) * (8 * d.size + 21) +
        (d.size + 2) * (d.size + 6) = (d.size + 2) * (13 * d.size + 41) := by ring
    have hE : 2 * (d.size + 6) ≤ (d.size + 2) * (d.size + 6) := Nat.mul_le_mul_right _ (by omega)
    omega
  · have hpre := Eval.cons (Eval.cons (Eval.var_of_get (env := [d]) (i := 0) (v := d) (by simp))
      (Eval.nil [d])) (Eval.nil [d])
    have h₁' : Eval (Data.cons (.cons d .nil) .nil :: [d]) (.loop toBitsBody) (encode acc) t₁ := h₁
    have h₂' : Eval (encode acc :: Data.cons (.cons d .nil) .nil :: [d]) revProg (encode d.toBits) t₂ := by
      rw [← hacc, encode_bitStr_eq_list, encode_bitStr_eq_list, List.map_reverse]
      exact Eval.append_of_wellScoped h₂ revProg_wellScoped _
    exact Eval.let_ hpre (Eval.let_ h₁' h₂')

end Prog

/-- The bits of a tree, in polynomial time. -/
noncomputable def PolyTimeFun.toBits : PolyTimeFun Data BitStr where
  toFun := Data.toBits
  code := Prog.toBitsProg
  closed := Prog.toBitsProg_wellScoped
  timeBound := (X + 2) * (13 * X + 41)
  computes d := by
    obtain ⟨t, ht, hrun⟩ := Prog.toBitsProg_runs d
    exact ⟨t, by simpa using ht, hrun⟩

@[simp] theorem PolyTimeFun.toBits_apply (d : Data) : PolyTimeFun.toBits d = d.toBits := rfl

end MIPRE.Cost


