-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Semidecide
-- name    : MIPRE_Foundations_Cost_Semidecide
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:25:37.639839+00:00
-- url     : https://prove2.me/theorems/f6126747-3546-48bf-96ed-a3075a7cfe8c
-- title:
--   Recursively enumerable sets of bit strings are halting sets of the ambient model
-- statement:
--   This bundle holds the module identifying recursively enumerable predicates on bit strings with halting sets of programs of the ambient cost model. Its definitions fall in two groups. On the Mathlib side (`Turing.ToPartrec.Code`): `swapCode`, the code $[a, b, rest] \mapsto [b, a, rest]$; `stepFun`, the function on vectors of length $2$ with $[acc, n] \mapsto \mathrm{pair}\,n\,acc + 1$; `loopBody cg`, the body of a folding loop that, given a step code $cg$, continues from $[acc, n+1, rest]$ to $[\mathrm{pair}\,n\,acc + 1, rest]$ and stops on $[acc]$; `foldEnc`, the fold pairing the entries of a list onto an accumulator from the left; and `convCode cg`, which on $w.\mathrm{map}\,(\cdot + 1)$ returns $[\mathrm{foldEnc}\,w\,0]$. On the ambient side: `shiftRevBody`, a loop body that, on the state $(xs, acc)$, stops with $acc$ when $xs$ is empty and otherwise moves $\mathrm{cons}\,\mathrm{nil}\,(\mathrm{head}\,xs)$ onto $acc$, and `shiftRevProg`, computing on $\mathrm{list}\,l$ the list $\mathrm{reverse}\,(l.\mathrm{map}\,(\mathrm{cons}\,\mathrm{nil}))$: on an encoded bit string, the reversed list of its bits shifted up by one. Main theorem: for every predicate $p$ on bit strings with `REPred p`,
--
--   $$\exists\, S : \mathrm{Prog},\quad S.\mathrm{WellScoped}\,1 \;\wedge\; \forall x : \mathrm{BitStr},\ \mathrm{Halts}\,S\,(\mathrm{encode}\,x) \longleftrightarrow p\,x.$$
--
--   The other embedded lemmas are the evaluation equations of these codes, the identity $\mathrm{foldEnc}\,(l.\mathrm{map}\,\mathrm{encode})\,(\mathrm{encode}\,m) = \mathrm{encode}\,(\mathrm{reverse}\,l \mathbin{+\!\!+} m)$, the existence of a step code and of a code halting on the shifted reversed string exactly on $p$, the well-scopedness and runs of the shift program, its relation to `encL`, and the primitive recursiveness of `Data.ofBool` and of the encoding of bit strings. The theorem is the hypothesis `hS` of the compressibility criterion, for $p$ the complement of the class $B$.
--
--   **Formalization Note** `REPred` is Mathlib's; `Halts S d := ∃ r t, Eval [d] S r t`; `encode x : Data` is the `cons`-chain of the `Data.ofBool` bits of `x`, `false` being the numeral `nil`. The shift is needed because a `ToPartrec` code reads `[]` and `0 :: v` alike, so no translated code separates `x` from `x ++ [false]`; `Data.cons_nil_ofBool` states `cons nil (ofBool b) = ofNat (encode b + 1)`. `shiftRevBody`, `shiftRevProg` are `def`s of type `Prog`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Semidecide.lean; blueprint lem:value-lower-approx

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Semidecide.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Eval_of_append_of_wellScoped
import Theorems.Thm_MIPRE_Cost_Prog_ofCode_wellScoped

/-!
# Recursively enumerable sets of bit strings are halting sets of the ambient model

`exists_semidecider`: for every recursively enumerable predicate `p` on bit strings (Mathlib's
`REPred`) there is a well-scoped program `S` of the ambient model that halts on the encoding
`encode x` of a bit string `x` exactly when `p x`. This is the form in which the
compressibility criterion (`MIPRE.Cost.compressibility_criterion`) consumes semidecidability
— its hypothesis `hS : ∀ x, Halts S (encode x) ↔ x ∉ B` — and, with `rePred_halts` (the
halting set of a program on encoded strings is recursively enumerable), it identifies `REPred`
on bit strings with the halting sets of the model (`MIPRE.isRE_iff`).

The route is that of `exists_compile`: through `Turing.ToPartrec.Code` and its translation
`Prog.ofCode`, with one obstacle. A `ToPartrec` code cannot see trailing zeros of its input
list (its primitives read `[]` and `0 :: v` alike), whereas the bit `false` encodes as
`nil = ofNat 0`, so no translated code can separate `x` from `x ++ [false]`. So `S` first shifts
every bit up by one — `shiftRevProg`, a `loop`, which reverses the list on the way as loops
naturally do — producing the `encL`-encoding of a list of ones and twos, which a `ToPartrec`
loop (`BitCode.convCode`) folds into the Mathlib code number `Encodable.encode x` of the
original string; a `ToPartrec` code for the r.e. predicate, from
`Turing.ToPartrec.Code.exists_code`, then runs on that number.
-/

namespace MIPRE.Cost

open Turing.ToPartrec (Code)

/-! ## A `ToPartrec` code reading a bit string off a list of ones and twos -/

namespace BitCode

open Turing.ToPartrec.Code

/-- `[a, b, rest...] ↦ [b, a, rest...]` (and `[a] ↦ [0, a]`). -/
def swapCode : Code := .cons (head.comp Code.tail) (.cons head (Code.tail.comp Code.tail))

set_option backward.isDefEq.respectTransparency false in
theorem swapCode_eval (a b : ℕ) (rest : List ℕ) :
    swapCode.eval (a :: b :: rest) = pure (b :: a :: rest) := by
  simp [swapCode]

set_option backward.isDefEq.respectTransparency false in
theorem swapCode_eval_single (a : ℕ) : swapCode.eval [a] = pure [0, a] := by
  simp [swapCode]

/-- The step of the fold, `[acc, n] ↦ pair n acc + 1`, as a function on vectors: it is
`Encodable.encode (b :: l)` from `n = encode b` and `acc = encode l`. -/
def stepFun (v : List.Vector ℕ 2) : ℕ := Nat.pair (v.get 1) v.head + 1

theorem primrec_stepFun : Primrec stepFun :=
  Primrec.succ.comp (Primrec₂.natPair.comp
    (Primrec.vector_get.comp Primrec.id (Primrec.const 1)) Primrec.vector_head)

/-- A `ToPartrec` code for the step of the fold. -/
theorem exists_stepCode :
    ∃ c : Code, ∀ acc n : ℕ, c.eval [acc, n] = pure [Nat.pair n acc + 1] := by
  obtain ⟨c, hc⟩ := exists_code (Nat.Partrec'.prim (Nat.Primrec'.of_prim primrec_stepFun))
  exact ⟨c, fun acc n => hc ⟨[acc, n], rfl⟩⟩

/-- Body of the folding loop, given a step code `cg`: on `[acc, n + 1, rest...]` continue with
`[pair n acc + 1, rest...]`; on `[acc]` (or `[acc, 0, ...]`) stop with `[acc]`. -/
def loopBody (cg : Code) : Code :=
  (Code.case (Code.cons zero (Code.cons head nil))
    (Code.cons (succ.comp zero)
      (Code.cons (cg.comp (Code.cons (head.comp Code.tail) (Code.cons head nil)))
        (Code.tail.comp Code.tail)))).comp swapCode

set_option backward.isDefEq.respectTransparency false in
theorem loopBody_eval_stop (cg : Code) (acc : ℕ) : (loopBody cg).eval [acc] = pure [0, acc] := by
  simp [loopBody, swapCode_eval_single]

set_option backward.isDefEq.respectTransparency false in
theorem loopBody_eval_step (cg : Code)
    (hcg : ∀ acc n : ℕ, cg.eval [acc, n] = pure [Nat.pair n acc + 1]) (acc n : ℕ)
    (rest : List ℕ) :
    (loopBody cg).eval (acc :: (n + 1) :: rest) = pure (1 :: (Nat.pair n acc + 1) :: rest) := by
  simp [loopBody, swapCode_eval, hcg]

/-- The fold computed by the loop: `foldEnc [n₁, …, nₖ] acc` pairs the entries onto the
accumulator from the left. -/
def foldEnc : List ℕ → ℕ → ℕ
  | [], acc => acc
  | n :: w, acc => foldEnc w (Nat.pair n acc + 1)

set_option backward.isDefEq.respectTransparency false in
theorem fix_loopBody_eval (cg : Code)
    (hcg : ∀ acc n : ℕ, cg.eval [acc, n] = pure [Nat.pair n acc + 1]) :
    ∀ (w : List ℕ) (acc : ℕ),
      (Code.fix (loopBody cg)).eval (acc :: w.map (· + 1)) = pure [foldEnc w acc]
  | [], acc => by
    rw [fix_eval]
    refine Part.eq_some_iff.2 (PFun.fix_stop ?_)
    simp [loopBody_eval_stop, foldEnc]
  | n :: w, acc => by
    rw [fix_eval, List.map_cons,
      PFun.fix_fwd_eq (a' := (Nat.pair n acc + 1) :: w.map (· + 1)), ← fix_eval,
      fix_loopBody_eval cg hcg w]
    · rfl
    · simp [loopBody_eval_step cg hcg]

/-- The conversion code: on a list of positive naturals `w.map (· + 1)` it returns
`[foldEnc w 0]`. -/
def convCode (cg : Code) : Code := (Code.fix (loopBody cg)).comp zero'

set_option backward.isDefEq.respectTransparency false in
theorem convCode_eval (cg : Code)
    (hcg : ∀ acc n : ℕ, cg.eval [acc, n] = pure [Nat.pair n acc + 1]) (w : List ℕ) :
    (convCode cg).eval (w.map (· + 1)) = pure [foldEnc w 0] := by
  have h := fix_loopBody_eval cg hcg w 0
  rw [convCode, comp_eval]
  simp only [zero'_eval, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some]
  exact h

/-- Folding the codes of the bits of `l` onto the code of `m` yields the code of
`l.reverse ++ m`. -/
theorem foldEnc_encode (l m : List Bool) :
    foldEnc (l.map Encodable.encode) (Encodable.encode m) = Encodable.encode (l.reverse ++ m) := by
  induction l generalizing m with
  | nil => simp [foldEnc]
  | cons b l ih =>
    rw [List.map_cons, foldEnc, ← Nat.succ_eq_add_one, ← Encodable.encode_list_cons, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

set_option backward.isDefEq.respectTransparency false in
/-- An r.e. predicate on bit strings is the halting set of a `ToPartrec` code on the list of
shifted bit codes of the reversed string. -/
theorem exists_code_bitStr {p : BitStr → Prop} (hp : REPred p) :
    ∃ c : Code, ∀ x : BitStr,
      (c.eval ((x.reverse.map Encodable.encode).map (· + 1))).Dom ↔ p x := by
  obtain ⟨cg, hcg⟩ := exists_stepCode
  -- the r.e. predicate on code numbers, as a partial function of a one-entry vector
  let f₁ : List.Vector ℕ 1 →. ℕ := fun v =>
    ((Encodable.decode v.head : Option BitStr) : Part BitStr).bind fun x =>
      (Part.assert (p x) fun _ => Part.some ()).map fun _ => (0 : ℕ)
  have hf₁ : Partrec f₁ :=
    Partrec.bind (Computable.ofOption (Computable.decode.comp Computable.vector_head))
      ((hp.comp Computable.snd).map (Computable.const 0).to₂)
  obtain ⟨cm, hcm⟩ := exists_code (Nat.Partrec'.of_part hf₁)
  refine ⟨cm.comp (convCode cg), fun x => ?_⟩
  have h1 : (convCode cg).eval ((x.reverse.map Encodable.encode).map (· + 1)) =
      pure [Encodable.encode x] := by
    rw [convCode_eval cg hcg]
    have := foldEnc_encode x.reverse []
    simp only [List.reverse_reverse, List.append_nil, Encodable.encode_list_nil] at this
    rw [this]
  have h2 := hcm ⟨[Encodable.encode x], rfl⟩
  have h3 : (cm.comp (convCode cg)).eval ((x.reverse.map Encodable.encode).map (· + 1)) =
      pure <$> f₁ ⟨[Encodable.encode x], rfl⟩ := by
    rw [comp_eval]
    simp only [h1, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some]
    exact h2
  rw [h3]
  have hhead : List.Vector.head (⟨[Encodable.encode x], rfl⟩ : List.Vector ℕ 1) =
      Encodable.encode x := rfl
  have hv : f₁ ⟨[Encodable.encode x], rfl⟩ =
      (Part.assert (p x) fun _ => Part.some ()).map fun _ => (0 : ℕ) := by
    simp only [f₁, hhead, Encodable.encodek, Part.coe_some, Part.bind_some]
  rw [hv, Part.map_eq_map]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩

end BitCode

/-! ## Shifting the bits up by one, in the ambient model -/

namespace Prog

/-- Body of `shiftRevProg`: on state `cons xs acc`, stop with `acc` if `xs` is empty, otherwise
move `cons nil (head xs)` onto `acc`. -/
def shiftRevBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.var 1))
    (.cons (.cons .nil .nil) (.cons (.var 1) (.cons (.cons .nil (.var 0)) (.var 3)))))

/-- `shiftRevProg` on `list l` computes `list ((l.map (cons nil)).reverse)`: on an encoded bit
string, the reversed list of its bits shifted up by one (`cons_nil_ofBool`). -/
def shiftRevProg : Prog := .let_ (.cons (.var 0) .nil) (.loop shiftRevBody)

theorem shiftRevBody_wellScoped : shiftRevBody.WellScoped 1 := by
  simp [shiftRevBody, WellScoped]

theorem shiftRevProg_wellScoped : shiftRevProg.WellScoped 1 :=
  ⟨⟨Nat.zero_lt_one, trivial⟩, ⟨by omega, shiftRevBody_wellScoped.mono (by omega) _⟩⟩

/-- One iteration of `shiftRevBody` on a non-empty list. -/
theorem shiftRevBody_step (h : Data) (l acc : List Data) :
    ∃ t, Eval [.cons (.list (h :: l)) (.list acc)] shiftRevBody
      (.cons (.cons .nil .nil) (.cons (.list l) (.list (.cons .nil h :: acc)))) t :=
  ⟨_, Eval.elim_cons (i := 0) (n := .nil) (a := .list (h :: l)) (b := .list acc) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.var 1)) (a := h) (b := .list l) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
        (Eval.cons (Eval.var_of_get (i := 1) (v := .list l) (by simp))
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := h) (by simp)))
            (Eval.var_of_get (i := 3) (v := .list acc) (by simp))))))⟩

/-- The stopping iteration of `shiftRevBody` on the empty list. -/
theorem shiftRevBody_stop (acc : List Data) :
    ∃ t, Eval [.cons (.list []) (.list acc)] shiftRevBody (.cons .nil (.list acc)) t :=
  ⟨_, Eval.elim_cons (i := 0) (n := .nil) (a := .list []) (b := .list acc) (by simp)
    (Eval.elim_nil (i := 0) (c := _) (by simp)
      (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := .list acc) (by simp))))⟩

theorem shiftRevLoop_runs (l acc : List Data) (env : Env) :
    ∃ t, Eval (.cons (.list l) (.list acc) :: env) (.loop shiftRevBody)
      (.list ((l.map (Data.cons .nil)).reverse ++ acc)) t := by
  induction l generalizing acc with
  | nil =>
    obtain ⟨t, h⟩ := shiftRevBody_stop acc
    exact ⟨_, by simpa using
      Eval.loop_stop (Eval.append_of_wellScoped h shiftRevBody_wellScoped env)⟩
  | cons h l ih =>
    obtain ⟨t, hrun⟩ := ih (.cons .nil h :: acc)
    obtain ⟨s, hstep⟩ := shiftRevBody_step h l acc
    have := Eval.loop_step (Eval.append_of_wellScoped hstep shiftRevBody_wellScoped env) hrun
    exact ⟨_, by simpa [List.append_assoc] using this⟩

theorem shiftRevProg_runs (l : List Data) :
    ∃ t, Eval [Data.list l] shiftRevProg (.list ((l.map (Data.cons .nil)).reverse)) t := by
  obtain ⟨t, hrun⟩ := shiftRevLoop_runs l [] [Data.list l]
  exact ⟨_, Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := .list l) (by simp)) (Eval.nil _))
    (by simpa using hrun)⟩

end Prog

/-- A bit shifted up by one is the unary numeral of its code plus one: `false ↦ ofNat 1`,
`true ↦ ofNat 2`. -/
theorem Data.cons_nil_ofBool (b : Bool) :
    Data.cons .nil (Data.ofBool b) = Data.ofNat (Encodable.encode b + 1) := by
  cases b <;> rfl

theorem encode_bitStr_eq (x : BitStr) : (encode x : Data) = Data.list (x.map Data.ofBool) :=
  Data.ofList_eq_list _ _

/-- The output of `shiftRevProg` on an encoded bit string is the `encL`-encoding of the shifted
codes of the bits of the reversed string. -/
theorem Data.list_shift_eq_encL (x : BitStr) :
    Data.list (((x.map Data.ofBool).map (Data.cons .nil)).reverse) =
      encL ((x.reverse.map Encodable.encode).map (· + 1)) := by
  simp only [encL, List.map_map, List.map_reverse, Function.comp_def, Data.cons_nil_ofBool]

/-! ## The semidecider -/

/-- **Recursively enumerable predicates are halting sets.** For every r.e. predicate `p` on bit
strings there is a well-scoped program halting on `encode x` exactly when `p x`: the hypothesis
`hS` of `compressibility_criterion`, for `p := (· ∉ B)`. -/
theorem exists_semidecider {p : BitStr → Prop} (hp : REPred p) :
    ∃ S : Prog, S.WellScoped 1 ∧ ∀ x : BitStr, Halts S (encode x) ↔ p x := by
  obtain ⟨c, hc⟩ := BitCode.exists_code_bitStr hp
  refine ⟨.let_ Prog.shiftRevProg (Prog.ofCode c),
    ⟨Prog.shiftRevProg_wellScoped, (Prog.ofCode_wellScoped c).mono (by omega) _⟩, fun x => ?_⟩
  rw [← hc x, ← Prog.ofCode_halts_iff, ← Data.list_shift_eq_encL, encode_bitStr_eq]
  obtain ⟨s, hpre⟩ := Prog.shiftRevProg_runs (x.map Data.ofBool)
  constructor
  · rintro ⟨r, t, h⟩
    cases h with
    | let_ h₁ h₂ =>
      obtain ⟨rfl, -⟩ := h₁.deterministic hpre
      exact ⟨r, _, Eval.of_append_of_wellScoped (env := [_]) (extra := [_]) h₂
        (Prog.ofCode_wellScoped c)⟩
  · rintro ⟨r, t, h⟩
    exact ⟨r, _, Eval.let_ hpre (Eval.append_of_wellScoped h (Prog.ofCode_wellScoped c) _)⟩

/-! ## The converse: halting sets are recursively enumerable -/

theorem Data.primrec_ofBool : Primrec Data.ofBool :=
  (Primrec.cond Primrec.id (Primrec.const (Data.cons .nil .nil)) (Primrec.const .nil)).of_eq
    fun b => by cases b <;> rfl

theorem Data.ofList_eq_foldr {α : Type*} (f : α → Data) (l : List α) :
    Data.ofList f l = l.foldr (fun a d => Data.cons (f a) d) .nil := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Data.ofList, ih]

/-- The encoding of bit strings as data is primitive recursive. -/
theorem primrec_encode_bitStr : Primrec fun x : BitStr => (encode x : Data) := by
  have hh : Primrec₂ fun (_ : BitStr) (p : Bool × Data) => Data.cons (Data.ofBool p.1) p.2 :=
    Data.primrec_cons.comp (Data.primrec_ofBool.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.id (Primrec.const .nil) hh).of_eq fun x =>
    (Data.ofList_eq_foldr _ _).symm

end MIPRE.Cost


