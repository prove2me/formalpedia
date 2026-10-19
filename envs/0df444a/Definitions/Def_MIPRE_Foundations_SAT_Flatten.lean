-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_Flatten
-- name    : MIPRE_Foundations_SAT_Flatten
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:47.919383+00:00
-- url     : https://prove2.me/theorems/bdd385bd-8387-4c97-9e6b-1ecdcfb51946
-- title:
--   Definitions of Flatten: Flattening a formula to a circuit, in polynomial time A formula is encoded as its post-order serialization (`Fml.rpn`),…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.Flatten` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Flattening a formula to a circuit, in polynomial time. A formula is encoded as its post-order serialization (`Fml.rpn`), and the circuit of a formula (`Fml.flattenAt 0`) is computed from that serialization by a single left-to-right scan with a stack of gate indices (`flStep`, `flatten`): an input or constant node emits its gate and pushes the gate's index; a connective pops the indices of its arguments, emits the gate and pushes the new index. The scan is a fold, so the program is a `PolyTimeFun.foldl` of the step (`PolyTimeFun.casesNode` dispatches on the node), and `Fml.toCircuitF` is the…
--
--   **Definitions** (24): `MIPRE.SAT.FlProg.casesNodeProg` (Dispatch on the node of an input `(a, nd)`: the environment after the two `elim`s is `[tag, payload, a, nd, input]`, and the unary tag is…); `MIPRE.SAT.FlProg.cnConst`; `MIPRE.SAT.FlProg.cnInp` (The branches of `casesNodeProg`, in the environments described there.); `MIPRE.SAT.FlProg.cnRest1`; `MIPRE.SAT.FlProg.cnRest2`; `MIPRE.SAT.FlProg.cnRest3`; `MIPRE.SAT.FlProg.cnTag`; `MIPRE.SAT.FlState` (The state of the scan: the stack of gate indices, the gates so far (reversed), and the number of gates so far.); `MIPRE.SAT.Fml.toCircuitF` (**The circuit of a formula on `n` inputs, in polynomial time.**); `MIPRE.SAT.Gate.andF`; `MIPRE.SAT.Gate.constF`; `MIPRE.SAT.Gate.inputF` (The gate constructors as polynomial-time functions.); `MIPRE.SAT.Gate.notF`; `MIPRE.SAT.Gate.orF`; `MIPRE.SAT.Gate.payload` (The payload of a gate: the input index of an input gate.); `MIPRE.SAT.PolyTimeFun.casesNode` (Case analysis on a node component.); `MIPRE.SAT.PolyTimeFun.casesNodeFun` (The function of `casesNode`.); `MIPRE.SAT.flBinF` (The step of the scan on a binary connective: pop two indices, emit the gate, push.); `MIPRE.SAT.flLeafF` (The step of the scan on a leaf: push the counter, emit the gate, increment.); `MIPRE.SAT.flNotF` (The step of the scan on a negation.); `MIPRE.SAT.flStep` (One step of the scan.); `MIPRE.SAT.flStepF` (The step of the scan, as a polynomial-time function.); `MIPRE.SAT.flatten` (The gates of a serialization.); and -5 more.
--
--   **Embedded lemmas** (26): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `casesNodeProg_and`, `casesNodeProg_const`, `casesNodeProg_inp`, `casesNodeProg_not`, `casesNodeProg_or`, `casesNodeProg_wellScoped`, `toCircuitF_apply`, `casesNode_and`, `casesNode_const`, `casesNode_inp`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.Flatten` (`MIPRE/Foundations/SAT/Flatten.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 11 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Flatten.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Flatten.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Theorems.Thm_MIPRE_SAT_Fml_Node_encode_and
import Theorems.Thm_MIPRE_SAT_Fml_Node_encode_not
import Theorems.Thm_MIPRE_SAT_Fml_Node_encode_or
import Theorems.Thm_MIPRE_SAT_Fml_size_pos

/-!
# Flattening a formula to a circuit, in polynomial time

A formula is encoded as its post-order serialization (`Fml.rpn`), and the circuit of a
formula (`Fml.flattenAt 0`) is computed from that serialization by a single left-to-right
scan with a stack of gate indices (`flStep`, `flatten`): an input or constant node emits its
gate and pushes the gate's index; a connective pops the indices of its arguments, emits the
gate and pushes the new index. The scan is a fold, so the program is a `PolyTimeFun.foldl`
of the step (`PolyTimeFun.casesNode` dispatches on the node), and `Fml.toCircuitF` is the
circuit of a formula on a given number of inputs as a polynomial-time function
(`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.SAT

open Cost Polynomial

/-! ## The scan -/

/-- The state of the scan: the stack of gate indices, the gates so far (reversed), and the
number of gates so far. -/
abbrev FlState : Type := List ℕ × List Gate × ℕ

/-- One step of the scan. -/
def flStep (s : FlState) : Fml.Node → FlState
  | .inp i => (s.2.2 :: s.1, Gate.input i :: s.2.1, s.2.2 + 1)
  | .const b => (s.2.2 :: s.1, Gate.const b :: s.2.1, s.2.2 + 1)
  | .and => match s.1 with
    | g :: f :: vs => (s.2.2 :: vs, Gate.and f g :: s.2.1, s.2.2 + 1)
    | _ => s
  | .or => match s.1 with
    | g :: f :: vs => (s.2.2 :: vs, Gate.or f g :: s.2.1, s.2.2 + 1)
    | _ => s
  | .not => match s.1 with
    | f :: vs => (s.2.2 :: vs, Gate.not f :: s.2.1, s.2.2 + 1)
    | _ => s

/-- The scan of the serialization of `f` from a state pushes the output index of `f` and
emits its gates. -/
theorem foldl_flStep_rpn : ∀ (f : Fml) (rest : List Fml.Node) (vs : List ℕ) (out : List Gate) (cnt : ℕ),
    (f.rpn ++ rest).foldl flStep (vs, out, cnt) =
      rest.foldl flStep ((cnt + f.size - 1) :: vs, (f.flattenAt cnt).reverse ++ out, cnt + f.size)
  | .inp i, rest, vs, out, cnt => by
    simp [Fml.rpn, Fml.flattenAt, Fml.size, flStep]
  | .const b, rest, vs, out, cnt => by
    simp [Fml.rpn, Fml.flattenAt, Fml.size, flStep]
  | .and f g, rest, vs, out, cnt => by
    have hfp := f.size_pos
    have hgp := g.size_pos
    simp only [Fml.rpn, List.append_assoc]
    rw [foldl_flStep_rpn f, foldl_flStep_rpn g, List.singleton_append, List.foldl_cons]
    simp only [flStep, Fml.flattenAt, Fml.size, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.append_assoc]
    have e1 : cnt + (f.size + g.size + 1) - 1 = cnt + f.size + g.size := by omega
    have e2 : cnt + (f.size + g.size + 1) = cnt + f.size + g.size + 1 := by omega
    rw [e1, e2, List.cons_append]
  | .or f g, rest, vs, out, cnt => by
    have hfp := f.size_pos
    have hgp := g.size_pos
    simp only [Fml.rpn, List.append_assoc]
    rw [foldl_flStep_rpn f, foldl_flStep_rpn g, List.singleton_append, List.foldl_cons]
    simp only [flStep, Fml.flattenAt, Fml.size, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.append_assoc]
    have e1 : cnt + (f.size + g.size + 1) - 1 = cnt + f.size + g.size := by omega
    have e2 : cnt + (f.size + g.size + 1) = cnt + f.size + g.size + 1 := by omega
    rw [e1, e2, List.cons_append]
  | .not f, rest, vs, out, cnt => by
    have hfp := f.size_pos
    simp only [Fml.rpn, List.append_assoc]
    rw [foldl_flStep_rpn f, List.singleton_append, List.foldl_cons]
    simp only [flStep, Fml.flattenAt, Fml.size, List.reverse_append, List.reverse_singleton,
      List.singleton_append]
    have e1 : cnt + (f.size + 1) - 1 = cnt + f.size := by omega
    have e2 : cnt + (f.size + 1) = cnt + f.size + 1 := by omega
    rw [e1, e2, List.cons_append]

/-- The gates of a serialization. -/
def flatten (l : List Fml.Node) : List Gate := ((l.foldl flStep ([], [], 0)).2.1).reverse

theorem flatten_rpn (f : Fml) : flatten f.rpn = f.flattenAt 0 := by
  unfold flatten
  have := foldl_flStep_rpn f [] [] [] 0
  rw [List.append_nil] at this
  rw [this]
  simp

/-! ## The size of the state along the scan -/

/-- The payload of a gate: the input index of an input gate. -/
def Gate.payload : Gate → ℕ
  | .input i => esize i
  | _ => 0

theorem esize_gate_le (g : Gate) : esize g ≤ (g.refs.map esize).sum + g.payload + 12 := by
  cases g with
  | input i =>
    show (Data.cons (.ofNat 0) (encode i)).size ≤ _
    simp [Gate.refs, Gate.payload, esize, Data.ofNat]; omega
  | const b =>
    show (Data.cons (.ofNat 1) (encode b)).size ≤ _
    cases b <;> simp [Gate.refs, Gate.payload, encode, Data.ofNat, Data.ofBool]
  | and u v =>
    show (Data.cons (.ofNat 2) (encode (u, v))).size ≤ _
    simp [Gate.refs, Gate.payload, esize, encode_prod, Data.ofNat]; omega
  | or u v =>
    show (Data.cons (.ofNat 3) (encode (u, v))).size ≤ _
    simp [Gate.refs, Gate.payload, esize, encode_prod, Data.ofNat]; omega
  | not u =>
    show (Data.cons (.ofNat 4) (encode u)).size ≤ _
    simp [Gate.refs, Gate.payload, esize, Data.ofNat]; omega

theorem esize_inp_node (i : ℕ) : esize (Fml.Node.inp i) = esize i + 2 := by
  show (Data.cons (.ofNat 0) (encode i)).size = _
  simp [esize, Data.ofNat]; omega

/-- Along the scan, every index on the stack is bounded, and so is the state. -/
theorem flStep_bounded (l : List Fml.Node) (E : ℕ) (hE : ∀ nd ∈ l, esize nd ≤ E) : ∀ (vs : List ℕ) (out : List Gate) (cnt D : ℕ),
    (∀ v ∈ vs, esize v ≤ D) → esize cnt ≤ D →
    let s := l.foldl flStep (vs, out, cnt)
    (∀ v ∈ s.1, esize v ≤ D + 4 * l.length) ∧ esize s.2.2 ≤ D + 4 * l.length ∧
      esize s.1 ≤ esize vs + l.length * (D + 4 * l.length + 1) ∧
      esize s.2.1 ≤ esize out + l.length * (2 * (D + 4 * l.length) + E + 13) := by
  induction l with
  | nil => intro vs out cnt D hvs hcnt; simpa using ⟨hvs, hcnt⟩
  | cons nd l ih =>
    intro vs out cnt D hvs hcnt
    have hnd : esize nd ≤ E := hE nd (List.mem_cons_self ..)
    have hE' : ∀ nd ∈ l, esize nd ≤ E := fun x hx => hE x (List.mem_cons_of_mem _ hx)
    simp only [List.foldl_cons, List.length_cons]
    -- the new state after one step is bounded with `D + 4`
    have key : ∀ (vs' : List ℕ) (out' : List Gate) (cnt' : ℕ),
        flStep (vs, out, cnt) nd = (vs', out', cnt') →
        (∀ v ∈ vs', esize v ≤ D + 4) ∧ esize cnt' ≤ D + 4 ∧
          esize vs' ≤ esize vs + (D + 4 + 1) ∧ esize out' ≤ esize out + (2 * (D + 4) + E + 13) := by
      intro vs' out' cnt' h
      have hc : esize (cnt + 1) ≤ D + 4 := (esize_succ_le cnt).trans (by omega)
      cases nd with
      | inp i =>
        simp only [flStep, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨?_, hc, ?_, ?_⟩
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · omega
          · exact (hvs v hv).trans (by omega)
        · simp only [esize_list_cons]; omega
        · have := esize_gate_le (Gate.input i)
          simp only [Gate.refs, Gate.payload, List.map_nil, List.sum_nil] at this
          rw [esize_inp_node] at hnd
          show esize (Gate.input i) + esize out + 1 ≤ _
          omega
      | const b =>
        simp only [flStep, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨?_, hc, ?_, ?_⟩
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · omega
          · exact (hvs v hv).trans (by omega)
        · simp only [esize_list_cons]; omega
        · have := esize_gate_le (Gate.const b)
          simp only [Gate.refs, Gate.payload, List.map_nil, List.sum_nil] at this
          show esize (Gate.const b) + esize out + 1 ≤ _
          omega
      | and =>
        simp only [flStep] at h
        rcases vs with _ | ⟨g, _ | ⟨f, vs⟩⟩
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨fun v hv => (hvs v hv).trans (by omega), hcnt.trans (by omega), by omega, by omega⟩
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨fun v hv => (hvs v hv).trans (by omega), hcnt.trans (by omega), by omega, by omega⟩
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          have hg := hvs g (by simp)
          have hf := hvs f (by simp)
          refine ⟨?_, hc, ?_, ?_⟩
          · intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · omega
            · exact (hvs v (by simp [hv])).trans (by omega)
          · simp only [esize_list_cons]; omega
          · have := esize_gate_le (Gate.and f g)
            simp only [Gate.refs, Gate.payload, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil] at this
            show esize (Gate.and f g) + esize out + 1 ≤ _
            omega
      | or =>
        simp only [flStep] at h
        rcases vs with _ | ⟨g, _ | ⟨f, vs⟩⟩
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨fun v hv => (hvs v hv).trans (by omega), hcnt.trans (by omega), by omega, by omega⟩
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨fun v hv => (hvs v hv).trans (by omega), hcnt.trans (by omega), by omega, by omega⟩
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          have hg := hvs g (by simp)
          have hf := hvs f (by simp)
          refine ⟨?_, hc, ?_, ?_⟩
          · intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · omega
            · exact (hvs v (by simp [hv])).trans (by omega)
          · simp only [esize_list_cons]; omega
          · have := esize_gate_le (Gate.or f g)
            simp only [Gate.refs, Gate.payload, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil] at this
            show esize (Gate.or f g) + esize out + 1 ≤ _
            omega
      | not =>
        simp only [flStep] at h
        rcases vs with _ | ⟨f, vs⟩
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨fun v hv => (hvs v hv).trans (by omega), hcnt.trans (by omega), by omega, by omega⟩
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          have hf := hvs f (by simp)
          refine ⟨?_, hc, ?_, ?_⟩
          · intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · omega
            · exact (hvs v (by simp [hv])).trans (by omega)
          · simp only [esize_list_cons]; omega
          · have := esize_gate_le (Gate.not f)
            simp only [Gate.refs, Gate.payload, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil] at this
            show esize (Gate.not f) + esize out + 1 ≤ _
            omega
    rcases hstep : flStep (vs, out, cnt) nd with ⟨vs', out', cnt'⟩
    obtain ⟨h1, h2, h3, h4⟩ := key vs' out' cnt' hstep
    obtain ⟨i1, i2, i3, i4⟩ := ih hE' vs' out' cnt' (D + 4) h1 h2
    refine ⟨fun v hv => (i1 v hv).trans (by omega), i2.trans (by omega), ?_, ?_⟩
    · refine i3.trans ?_
      have : l.length * (D + 4 + 4 * l.length + 1) ≤ l.length * (D + 4 * (l.length + 1) + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.add_mul, Nat.one_mul]
      generalize l.length * (D + 4 + 4 * l.length + 1) = P at *
      generalize l.length * (D + 4 * (l.length + 1) + 1) = Q at *
      omega
    · refine i4.trans ?_
      have : l.length * (2 * (D + 4 + 4 * l.length) + E + 13) ≤
          l.length * (2 * (D + 4 * (l.length + 1)) + E + 13) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.add_mul, Nat.one_mul]
      generalize l.length * (2 * (D + 4 + 4 * l.length) + E + 13) = P at *
      generalize l.length * (2 * (D + 4 * (l.length + 1)) + E + 13) = Q at *
      omega

/-! ## Dispatch on a node -/

namespace FlProg

/-- The branches of `casesNodeProg`, in the environments described there. -/
def cnInp (Fi : Prog) : Prog := .let_ (.cons (.var 2) (.var 1)) Fi
def cnConst (Fc : Prog) : Prog := .let_ (.cons (.var 4) (.var 3)) Fc
def cnRest3 (Fo Fn : Prog) : Prog := .elim 1 (Prog.callVar 8 Fo) (Prog.callVar 10 Fn)
def cnRest2 (Fa Fo Fn : Prog) : Prog := .elim 1 (Prog.callVar 6 Fa) (cnRest3 Fo Fn)
def cnRest1 (Fc Fa Fo Fn : Prog) : Prog := .elim 1 (cnConst Fc) (cnRest2 Fa Fo Fn)
def cnTag (Fi Fc Fa Fo Fn : Prog) : Prog := .elim 0 (cnInp Fi) (cnRest1 Fc Fa Fo Fn)

/-- Dispatch on the node of an input `(a, nd)`: the environment after the two `elim`s is
`[tag, payload, a, nd, input]`, and the unary tag is inspected one `nil` at a time. -/
def casesNodeProg (Fi Fc Fa Fo Fn : Prog) : Prog :=
  .elim 0 .nil (.elim 1 .nil (cnTag Fi Fc Fa Fo Fn))

theorem casesNodeProg_wellScoped {Fi Fc Fa Fo Fn : Prog} (hi : Fi.WellScoped 1)
    (hc : Fc.WellScoped 1) (ha : Fa.WellScoped 1) (ho : Fo.WellScoped 1) (hn : Fn.WellScoped 1) :
    (casesNodeProg Fi Fc Fa Fo Fn).WellScoped 1 := by
  simp [casesNodeProg, cnTag, cnRest1, cnRest2, cnRest3, cnInp, cnConst, Prog.callVar,
    Prog.WellScoped, hi.mono (show 1 ≤ 6 by omega) _, hc.mono (show 1 ≤ 8 by omega) _,
    ha.mono (show 1 ≤ 10 by omega) _, ho.mono (show 1 ≤ 12 by omega) _, hn.mono (show 1 ≤ 14 by omega) _]

variable {Fi Fc Fa Fo Fn : Prog}

theorem casesNodeProg_inp (hi : Fi.WellScoped 1) (ea : Data) (i : ℕ) {r : Data} {t : ℕ}
    (h : Eval [.cons ea (encode i)] Fi r t) :
    Eval [.cons ea (encode (Fml.Node.inp i))] (casesNodeProg Fi Fc Fa Fo Fn) r
      (ea.size + esize i + t + 7) := by
  have e := Eval.elim_cons (env := [Data.cons ea (encode (Fml.Node.inp i))]) (i := 0) (n := .nil)
    (a := ea) (b := encode (Fml.Node.inp i)) (by simp)
    (Eval.elim_cons (i := 1) (n := .nil) (a := .ofNat 0) (b := encode i) (by simp [Fml.Node.encode_inp])
      (Eval.elim_nil (i := 0) (c := cnRest1 Fc Fa Fo Fn) (by simp [Data.ofNat])
        (show Eval _ (cnInp Fi) _ _ from
          Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := ea) (by simp))
            (Eval.var_of_get (i := 1) (v := encode i) (by simp)))
            (Eval.append_of_wellScoped h hi _))))
  exact e.cast_cost (by simp only [esize]; omega)

theorem casesNodeProg_const (hc : Fc.WellScoped 1) (ea : Data) (b : Bool) {r : Data} {t : ℕ}
    (h : Eval [.cons ea (encode b)] Fc r t) :
    Eval [.cons ea (encode (Fml.Node.const b))] (casesNodeProg Fi Fc Fa Fo Fn) r
      (ea.size + esize b + t + 8) := by
  have e := Eval.elim_cons (env := [Data.cons ea (encode (Fml.Node.const b))]) (i := 0) (n := .nil)
    (a := ea) (b := encode (Fml.Node.const b)) (by simp)
    (Eval.elim_cons (i := 1) (n := .nil) (a := .ofNat 1) (b := encode b)
      (by simp [Fml.Node.encode_const])
      (Eval.elim_cons (i := 0) (n := cnInp Fi) (a := .nil) (b := .nil) (by simp [Data.ofNat])
        (Eval.elim_nil (i := 1) (c := cnRest2 Fa Fo Fn) (by simp)
          (show Eval _ (cnConst Fc) _ _ from
            Eval.let_ (Eval.cons (Eval.var_of_get (i := 4) (v := ea) (by simp))
              (Eval.var_of_get (i := 3) (v := encode b) (by simp)))
              (Eval.append_of_wellScoped h hc _)))))
  exact e.cast_cost (by simp only [esize]; omega)

theorem casesNodeProg_and (ha : Fa.WellScoped 1) (ea : Data) {r : Data} {t : ℕ}
    (h : Eval [ea] Fa r t) :
    Eval [.cons ea (encode Fml.Node.and)] (casesNodeProg Fi Fc Fa Fo Fn) r (ea.size + t + 7) := by
  have e := Eval.elim_cons (env := [Data.cons ea (encode Fml.Node.and)]) (i := 0) (n := .nil)
    (a := ea) (b := encode Fml.Node.and) (by simp)
    (Eval.elim_cons (i := 1) (n := .nil) (a := .ofNat 2) (b := .nil) (by simp [Fml.Node.encode_and])
      (Eval.elim_cons (i := 0) (n := cnInp Fi) (a := .nil) (b := .ofNat 1) (by simp [Data.ofNat])
        (Eval.elim_cons (i := 1) (n := cnConst Fc) (a := .nil) (b := .nil) (by simp [Data.ofNat])
          (Eval.elim_nil (i := 1) (c := cnRest3 Fo Fn) (by simp)
            (Prog.callVar_eval (i := 6) ha (by simp) h)))))
  exact e.cast_cost (by omega)

theorem casesNodeProg_or (ho : Fo.WellScoped 1) (ea : Data) {r : Data} {t : ℕ}
    (h : Eval [ea] Fo r t) :
    Eval [.cons ea (encode Fml.Node.or)] (casesNodeProg Fi Fc Fa Fo Fn) r (ea.size + t + 8) := by
  have e := Eval.elim_cons (env := [Data.cons ea (encode Fml.Node.or)]) (i := 0) (n := .nil)
    (a := ea) (b := encode Fml.Node.or) (by simp)
    (Eval.elim_cons (i := 1) (n := .nil) (a := .ofNat 3) (b := .nil) (by simp [Fml.Node.encode_or])
      (Eval.elim_cons (i := 0) (n := cnInp Fi) (a := .nil) (b := .ofNat 2) (by simp [Data.ofNat])
        (Eval.elim_cons (i := 1) (n := cnConst Fc) (a := .nil) (b := .ofNat 1) (by simp [Data.ofNat])
          (Eval.elim_cons (i := 1) (n := Prog.callVar 6 Fa) (a := .nil) (b := .nil)
            (by simp [Data.ofNat])
            (Eval.elim_nil (i := 1) (c := Prog.callVar 10 Fn) (by simp)
              (Prog.callVar_eval (i := 8) ho (by simp) h))))))
  exact e.cast_cost (by omega)

theorem casesNodeProg_not (hn : Fn.WellScoped 1) (ea : Data) {r : Data} {t : ℕ}
    (h : Eval [ea] Fn r t) :
    Eval [.cons ea (encode Fml.Node.not)] (casesNodeProg Fi Fc Fa Fo Fn) r (ea.size + t + 8) := by
  have e := Eval.elim_cons (env := [Data.cons ea (encode Fml.Node.not)]) (i := 0) (n := .nil)
    (a := ea) (b := encode Fml.Node.not) (by simp)
    (Eval.elim_cons (i := 1) (n := .nil) (a := .ofNat 4) (b := .nil) (by simp [Fml.Node.encode_not])
      (Eval.elim_cons (i := 0) (n := cnInp Fi) (a := .nil) (b := .ofNat 3) (by simp [Data.ofNat])
        (Eval.elim_cons (i := 1) (n := cnConst Fc) (a := .nil) (b := .ofNat 2) (by simp [Data.ofNat])
          (Eval.elim_cons (i := 1) (n := Prog.callVar 6 Fa) (a := .nil) (b := .ofNat 1)
            (by simp [Data.ofNat])
            (Eval.elim_cons (i := 1) (n := Prog.callVar 8 Fo) (a := .nil) (b := .nil)
              (by simp [Data.ofNat])
              (Prog.callVar_eval (i := 10) hn (by simp) h))))))
  exact e.cast_cost (by omega)

end FlProg

theorem esize_node_inp (i : ℕ) : esize (Fml.Node.inp i) = esize i + 2 := esize_inp_node i

theorem esize_node_const (b : Bool) : esize (Fml.Node.const b) = esize b + 4 := by
  show (Data.cons (.ofNat 1) (encode b)).size = _
  simp [esize, Data.ofNat]; omega

namespace PolyTimeFun

variable {α β : Type*} [SizedEncoding α] [SizedEncoding β]

/-- The function of `casesNode`. -/
def casesNodeFun (Fi : α × ℕ → β) (Fc : α × Bool → β) (Fa Fo Fn : α → β) : α × Fml.Node → β
  | (a, .inp i) => Fi (a, i)
  | (a, .const b) => Fc (a, b)
  | (a, .and) => Fa a
  | (a, .or) => Fo a
  | (a, .not) => Fn a

/-- Case analysis on a node component. -/
noncomputable def casesNode (Fi : PolyTimeFun (α × ℕ) β) (Fc : PolyTimeFun (α × Bool) β)
    (Fa Fo Fn : PolyTimeFun α β) : PolyTimeFun (α × Fml.Node) β where
  toFun := casesNodeFun Fi Fc Fa Fo Fn
  code := FlProg.casesNodeProg Fi.code Fc.code Fa.code Fo.code Fn.code
  closed := FlProg.casesNodeProg_wellScoped Fi.closed Fc.closed Fa.closed Fo.closed Fn.closed
  timeBound := X + Fi.timeBound + Fc.timeBound + Fa.timeBound + Fo.timeBound + Fn.timeBound + C 8
  computes p := by
    obtain ⟨a, nd⟩ := p
    cases nd with
    | inp i =>
      obtain ⟨t, ht, e⟩ := Fi.computes (a, i)
      refine ⟨esize a + esize i + t + 7, ?_, FlProg.casesNodeProg_inp Fi.closed _ i e⟩
      have := polynomial_eval_mono Fi.timeBound
        (show esize (a, i) ≤ esize (a, Fml.Node.inp i) by simp only [esize_prod, esize_node_inp]; omega)
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod,
        esize_node_inp] at this ht ⊢
      omega
    | const b =>
      obtain ⟨t, ht, e⟩ := Fc.computes (a, b)
      refine ⟨esize a + esize b + t + 8, ?_, FlProg.casesNodeProg_const Fc.closed _ b e⟩
      have := polynomial_eval_mono Fc.timeBound
        (show esize (a, b) ≤ esize (a, Fml.Node.const b) by
          simp only [esize_prod, esize_node_const]; omega)
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod,
        esize_node_const] at this ht ⊢
      omega
    | and =>
      obtain ⟨t, ht, e⟩ := Fa.computes a
      refine ⟨esize a + t + 7, ?_, FlProg.casesNodeProg_and Fa.closed _ e⟩
      have := polynomial_eval_mono Fa.timeBound
        (show esize a ≤ esize (a, Fml.Node.and) by simp only [esize_prod]; omega)
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod] at this ⊢
      omega
    | or =>
      obtain ⟨t, ht, e⟩ := Fo.computes a
      refine ⟨esize a + t + 8, ?_, FlProg.casesNodeProg_or Fo.closed _ e⟩
      have := polynomial_eval_mono Fo.timeBound
        (show esize a ≤ esize (a, Fml.Node.or) by simp only [esize_prod]; omega)
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod] at this ⊢
      omega
    | not =>
      obtain ⟨t, ht, e⟩ := Fn.computes a
      refine ⟨esize a + t + 8, ?_, FlProg.casesNodeProg_not Fn.closed _ e⟩
      have := polynomial_eval_mono Fn.timeBound
        (show esize a ≤ esize (a, Fml.Node.not) by simp only [esize_prod]; omega)
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod] at this ⊢
      omega

@[simp] theorem casesNode_inp (Fi : PolyTimeFun (α × ℕ) β) (Fc : PolyTimeFun (α × Bool) β)
    (Fa Fo Fn : PolyTimeFun α β) (a : α) (i : ℕ) :
    casesNode Fi Fc Fa Fo Fn (a, .inp i) = Fi (a, i) := rfl
@[simp] theorem casesNode_const (Fi : PolyTimeFun (α × ℕ) β) (Fc : PolyTimeFun (α × Bool) β)
    (Fa Fo Fn : PolyTimeFun α β) (a : α) (b : Bool) :
    casesNode Fi Fc Fa Fo Fn (a, .const b) = Fc (a, b) := rfl
@[simp] theorem casesNode_and (Fi : PolyTimeFun (α × ℕ) β) (Fc : PolyTimeFun (α × Bool) β)
    (Fa Fo Fn : PolyTimeFun α β) (a : α) : casesNode Fi Fc Fa Fo Fn (a, .and) = Fa a := rfl
@[simp] theorem casesNode_or (Fi : PolyTimeFun (α × ℕ) β) (Fc : PolyTimeFun (α × Bool) β)
    (Fa Fo Fn : PolyTimeFun α β) (a : α) : casesNode Fi Fc Fa Fo Fn (a, .or) = Fo a := rfl
@[simp] theorem casesNode_not (Fi : PolyTimeFun (α × ℕ) β) (Fc : PolyTimeFun (α × Bool) β)
    (Fa Fo Fn : PolyTimeFun α β) (a : α) : casesNode Fi Fc Fa Fo Fn (a, .not) = Fn a := rfl

end PolyTimeFun

/-! ## The scan as a polynomial-time function -/

/-- The gate constructors as polynomial-time functions. -/
noncomputable def Gate.inputF : PolyTimeFun ℕ Gate := PolyTimeFun.tagged 0 Gate.input fun _ => rfl
noncomputable def Gate.constF : PolyTimeFun Bool Gate := PolyTimeFun.tagged 1 Gate.const fun _ => rfl
noncomputable def Gate.andF : PolyTimeFun (ℕ × ℕ) Gate :=
  PolyTimeFun.tagged 2 (fun p => Gate.and p.1 p.2) fun _ => rfl
noncomputable def Gate.orF : PolyTimeFun (ℕ × ℕ) Gate :=
  PolyTimeFun.tagged 3 (fun p => Gate.or p.1 p.2) fun _ => rfl
noncomputable def Gate.notF : PolyTimeFun ℕ Gate := PolyTimeFun.tagged 4 Gate.not fun _ => rfl

open PolyTimeFun in
/-- The step of the scan on a leaf: push the counter, emit the gate, increment. -/
noncomputable def flLeafF {γ : Type*} [SizedEncoding γ] (G : PolyTimeFun γ Gate) :
    PolyTimeFun (FlState × γ) FlState :=
  ((snd.comp (snd.comp fst)).cons (fst.comp fst)).pair
    (((G.comp snd).cons (fst.comp (snd.comp fst))).pair (inc.comp (snd.comp (snd.comp fst))))

open PolyTimeFun in
/-- The step of the scan on a binary connective: pop two indices, emit the gate, push. The
state is presented as `((out, cnt), vs)` to `casesList`. -/
noncomputable def flBinF (G : PolyTimeFun (ℕ × ℕ) Gate) : PolyTimeFun FlState FlState :=
  (casesList ((const []).pair (PolyTimeFun.id _))
    ((casesList ((snd.cons (const [])).pair fst)
        (((snd.comp (fst.comp fst)).cons (snd.comp snd)).pair
          (((G.comp ((fst.comp snd).pair (snd.comp fst))).cons (fst.comp (fst.comp fst))).pair
            (inc.comp (snd.comp (fst.comp fst)))))).comp
      ((fst.pair (fst.comp snd)).pair (snd.comp snd)))).comp (snd.pair fst)

open PolyTimeFun in
/-- The step of the scan on a negation. -/
noncomputable def flNotF : PolyTimeFun FlState FlState :=
  (casesList ((const []).pair (PolyTimeFun.id _))
    (((snd.comp fst).cons (snd.comp snd)).pair
      (((Gate.notF.comp (fst.comp snd)).cons (fst.comp fst)).pair (inc.comp (snd.comp fst))))).comp
    (snd.pair fst)

theorem flBinF_apply_and (s : FlState) : flBinF Gate.andF s = flStep s .and := by
  obtain ⟨vs, out, cnt⟩ := s
  rcases vs with _ | ⟨g, _ | ⟨f, vs⟩⟩ <;> rfl

theorem flBinF_apply_or (s : FlState) : flBinF Gate.orF s = flStep s .or := by
  obtain ⟨vs, out, cnt⟩ := s
  rcases vs with _ | ⟨g, _ | ⟨f, vs⟩⟩ <;> rfl

theorem flNotF_apply (s : FlState) : flNotF s = flStep s .not := by
  obtain ⟨vs, out, cnt⟩ := s
  rcases vs with _ | ⟨f, vs⟩ <;> rfl

/-- The step of the scan, as a polynomial-time function. -/
noncomputable def flStepF : PolyTimeFun (FlState × Fml.Node) FlState :=
  PolyTimeFun.congr (PolyTimeFun.casesNode (flLeafF Gate.inputF) (flLeafF Gate.constF)
      (flBinF Gate.andF) (flBinF Gate.orF) flNotF)
    (fun p => flStep p.1 p.2) (by
      rintro ⟨s, nd⟩
      cases nd with
      | inp i => rfl
      | const b => rfl
      | and => exact flBinF_apply_and s
      | or => exact flBinF_apply_or s
      | not => exact flNotF_apply s)

@[simp] theorem flStepF_apply (p : FlState × Fml.Node) : flStepF p = flStep p.1 p.2 := rfl

theorem esize_flState (vs : List ℕ) (out : List Gate) (cnt : ℕ) :
    esize ((vs, out, cnt) : FlState) = esize vs + (esize out + esize cnt + 1) + 1 := rfl

/-- The Cobham condition of the scan. -/
theorem flStepF_bounded : PolyTimeFun.FoldBounded flStepF (C 40 * (X + 1) * (X + 1)) := by
  intro l s₀ pre xs hl
  obtain ⟨vs, out, cnt⟩ := s₀
  set N := esize (l, ((vs, out, cnt) : FlState)) with hN
  have hNe : N = esize l + (esize vs + (esize out + esize cnt + 1) + 1) + 1 := by
    simp [hN]
  have hpre : pre.length ≤ esize l := by
    have := congrArg List.length hl
    have := length_le_esize_list l
    simp only [List.length_append] at *; omega
  have hE : ∀ nd ∈ pre, esize nd ≤ esize l := fun nd hnd =>
    (by have := esize_mem_le (show nd ∈ l by rw [hl]; exact List.mem_append_left _ hnd); omega)
  have hvs : ∀ v ∈ vs, esize v ≤ N := fun v hv => by
    have := esize_mem_le hv; omega
  obtain ⟨-, h2, h3, h4⟩ := flStep_bounded pre (esize l) hE vs out cnt N hvs (by omega)
  show esize (List.foldl (fun s a => flStep s a) (vs, out, cnt) pre) ≤ _
  rcases hs : List.foldl (fun s a => flStep s a) (vs, out, cnt) pre with ⟨vs', out', cnt'⟩
  simp only [hs] at h2 h3 h4
  rw [esize_flState]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one]
  have hk : pre.length ≤ N := by omega
  have hl' : esize l ≤ N := by omega
  have hv0 : esize vs ≤ N := by omega
  have ho0 : esize out ≤ N := by omega
  have b1 : pre.length * (N + 4 * pre.length + 1) ≤ N * (6 * N) :=
    Nat.mul_le_mul hk (by omega)
  have b2 : pre.length * (2 * (N + 4 * pre.length) + esize l + 13) ≤ N * (24 * N) :=
    Nat.mul_le_mul hk (by omega)
  have b3 : N * (6 * N) + N * (24 * N) ≤ 30 * ((N + 1) * (N + 1)) := by
    have : N * (6 * N) + N * (24 * N) = 30 * (N * N) := by ring
    rw [this]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have b4 : 8 * N + 3 ≤ 10 * ((N + 1) * (N + 1)) := by
    have : N + 1 ≤ (N + 1) * (N + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [Nat.mul_assoc]
  omega

/-- The gates of a serialization, in polynomial time. -/
noncomputable def flattenF : PolyTimeFun (List Fml.Node) (List Gate) :=
  PolyTimeFun.congr (PolyTimeFun.reverse.comp ((PolyTimeFun.fst.comp PolyTimeFun.snd).comp
      ((PolyTimeFun.foldl flStepF _ flStepF_bounded).comp
        ((PolyTimeFun.id _).pair (PolyTimeFun.const (([], [], 0) : FlState))))))
    flatten (fun _ => rfl)

@[simp] theorem flattenF_apply (l : List Fml.Node) : flattenF l = flatten l := rfl

/-- **The circuit of a formula on `n` inputs, in polynomial time.** -/
noncomputable def Fml.toCircuitF : PolyTimeFun (ℕ × Fml) Circuit :=
  PolyTimeFun.cast (PolyTimeFun.fst.pair (flattenF.comp (Fml.rpnF.comp PolyTimeFun.snd)))
    (fun p => p.2.toCircuit p.1) (by
      rintro ⟨n, f⟩
      show encode (n, (f.toCircuit n).gates) = encode (n, flatten f.rpn)
      rw [flatten_rpn]; rfl)

@[simp] theorem Fml.toCircuitF_apply (p : ℕ × Fml) : Fml.toCircuitF p = p.2.toCircuit p.1 := rfl

end MIPRE.SAT


