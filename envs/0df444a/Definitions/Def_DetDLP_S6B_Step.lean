-- Prove2me | Definitions.Def_DetDLP_S6B_Step
-- name    : DetDLP_S6B_Step
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:04:20.210144+00:00
-- url     : https://prove2.me/theorems/535e03ff-0a52-4e19-ad57-8d1d5acd3e68
-- title:
--   Polynomial-time prefix-search driver for the contraction oracle
-- statement:
--   Each round parses the saved pair consisting of the original input and the current prefix. It reads the count in the returned one-coefficient polynomial, corrects for the two trivial products, and appends the selected bit. Unless all external coordinates are assigned, it emits the next canonical contraction query. The terminal round emits the binary integer represented by the first operand.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proposition 2.6 (pp. 10–11)

import Definitions.Def_DetDLP_S6B_Words
set_option autoImplicit false
namespace DetDLP.S6BStep
open Groundwork Groundwork.PolyT S6BWords S6BPrefix w4_M5Evaluator w5_M6DivisorConstraints
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.prodMk Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.mul Groundwork.PolyT.length Groundwork.PolyT.map P2M_Groundwork_PolyT_ite__226169acf219 P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_id__1c5d0f44cc8f pair_poly inst_poly threshold_poly w5_M6Sort.cw_poly

def readout (w p : Wd) := countWord (bval (p.take w.length))
def req (w p : Wd) := inst w (p ++ [false])
def next (w p : Wd) := if p.length < 4*w.length then false :: pair (pair w p) (req w p) else true :: readout w p

def unpack (w : Wd) := splitFrame w
@[simp] theorem unpack_pair (s a : Wd) : unpack (pair s a) = (s,a) := by simp [unpack,splitFrame_frame_append]
@[local fun_prop] theorem unpack_poly {α} [Enc α] {f : α → Wd} (hf : PolyT f) : PolyT (fun x => unpack (f x)) := Groundwork.PolyT.comp splitFrame_poly hf

def parse (a : Wd) := bval (unpack a.tail).1
@[simp] theorem parse_reply (n : ℕ) : parse (encodeNatListBin [n]) = n := by
  simp only [parse,encodeNatListBin,Encoding.encodeList,List.tail_cons,unpack,splitFrame_frame_append]
  exact countWord_value n

noncomputable def reply (w p : Wd) := encodeNatListBin [completionCount (ProductIs (d:=w.length) (bval w)) (pins (p++[false]))]

def step (x : Wd) :=
  let s := (unpack x).1
  let a := (unpack x).2
  if a.isEmpty then next s [] else
    let w := (unpack s).1
    let p := (unpack s).2
    next w (p ++ [!(decide (threshold w (p++[false]) < parse a))])

@[local fun_prop] theorem next_poly {α} [Enc α] {w p : α → Wd} (hw : PolyT w) (hp : PolyT p) : PolyT (fun x => next (w x) (p x)) := by unfold next req readout; fun_prop
attribute [local irreducible] next threshold unpack

theorem step_poly : PolyT step := by unfold step parse; fun_prop

@[simp] theorem step_init (w : Wd) : step (pair w []) = next w [] := by simp only [step,unpack_pair,List.isEmpty_nil,if_true]
@[simp] theorem step_reply (w p : Wd) : step (pair (pair w p) (reply w p)) = next w (advance (query w.length (bval w)) p) := by
  simp only [step,unpack_pair,reply,show ∀ n : ℕ, (encodeNatListBin [n]).isEmpty = false from fun _ => rfl,Bool.false_eq_true,if_false,parse_reply,advance,query,correctedOracle,threshold_eq]

private theorem read_bits (p : Wd) (d : ℕ) : bval (p.take d) = bitsToNat (fun i : Fin d => p[i.val]?.getD false) := by
  induction d generalizing p with
  | zero => simp [bitsToNat,bval]
  | succ d ih =>
    rw [← Fin.cons_self_tail (fun i : Fin (d+1) => p[i.val]?.getD false),bitsToNat_cons]
    cases p with
    | nil => simp [bval,Fin.tail_def,bitsToNat]
    | cons b p => simp [bval_cons,ih,Fin.tail_def]; cases b <;> simp <;> omega

theorem readout_eq (w : Wd) : readout w (grow (query w.length (bval w)) (4*w.length) []) = countWord (answer w.length (bval w)) := by rw [readout,read_bits]; rfl
end DetDLP.S6BStep


