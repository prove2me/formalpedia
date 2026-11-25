-- Prove2me | Definitions.Def_DetDLP_S8E_ECDecoder
-- name    : DetDLP_S8E_ECDecoder
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:38:09.246789+00:00
-- url     : https://prove2.me/theorems/b8771620-4e59-48a7-b944-4a4b4522b791
-- title:
--   EC prefix decoder: ECDecoder
-- statement:
--   Word-level components and correctness interfaces for elliptic-curve decomposition by exact prefix counts.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_S8A_FpPrefixStep
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DetDLP.s8e
open M89S1 m89_enum_words m89_decode_step Groundwork Groundwork.PolyT w4_M5Evaluator
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.prodMk
  Groundwork.PolyT.map Groundwork.PolyT.flatMap Groundwork.PolyT.filter Groundwork.PolyT.length Groundwork.PolyT.mul Groundwork.PolyT.div
  P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_id__1c5d0f44cc8f
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_ite__226169acf219
  pair_poly fields_poly enc_poly indices_poly co_poly w5_M6Sort.decode_poly w5_M6Sort.encode_poly splitFrame_comp

def onePoint (b : ℕ) (z : Word) := encodeNatListBin [if z.headD false then 1 else 0, coord z.tail b 0, coord z.tail b 1]
@[local fun_prop] theorem point_poly {α : Type} [Enc α] {b : α → ℕ} {w : α → Word} (hb : PolyT b) (hw : PolyT w) : PolyT (fun x => onePoint (b x) (w x)) := by unfold onePoint; fun_prop

def finish (b : ℕ) (w : Word) := Encoding.encodeList id (((indices w).filter (fun i => decide (i < w.length/(2*b+1)))).map (fun i => onePoint b ((w.drop (i*(2*b+1))).take (2*b+1))))
@[local fun_prop] theorem fin_poly {α : Type} [Enc α] {b : α → ℕ} {w : α → Word} (hb : PolyT b) (hw : PolyT w) : PolyT (fun x => finish (b x) (w x)) := by unfold finish; apply enc_poly; apply Groundwork.PolyT.map <;> fun_prop

def advance (px plan pref : Word) :=
  let ns := fields px
  let extras := fields plan.tail
  let p := ns.getD 0 []
  let target := ns.getD 1 []
  let seed := extras.getD 1 []
  let b := ((w5_M6Sort.decode p |>.getD 0 0) - 1).bits.length
  if pref.length < seed.length + seed.length / (2*b) then
    false :: pair (state px plan pref) (queryWord 6 p [extras.getD 0 [],seed,target,pref ++ [false]])
  else true :: finish b pref

@[local fun_prop] theorem advance_poly {α : Type} [Enc α] {u v w : α → Word} (hu : PolyT u) (hv : PolyT v) (hw : PolyT w) : PolyT (fun x => advance (u x) (v x) (w x)) := by
  unfold advance state queryWord; dsimp only; fun_prop

def step (input : Word) :=
  let sx := splitFrame input
  let fs := fields sx.1
  let px := fs.getD 0 []
  let plan := fs.getD 1 []
  if plan.headD false then
    let pref := if sx.2.length = 0 then [] else (fs.getD 2 []) ++ [decide ((w5_M6Sort.decode sx.2).getD 0 0 = 0)]
    advance px plan pref
  else true :: Encoding.encodeList id [(fields px).getD 1 [],encodeNatListBin [1,0,0],encodeNatListBin [1,0,0],encodeNatListBin [1,0,0]]

theorem step_poly : PolyT step := by unfold step; dsimp only; fun_prop

@[simp] theorem step_none (curve x : Word) : step (pair (Encoding.encodeList id [Encoding.encodeList id [curve,x],[false]]) []) = true :: Encoding.encodeList id [x,encodeNatListBin [1,0,0],encodeNatListBin [1,0,0],encodeNatListBin [1,0,0]] := by simp [step]

@[simp] theorem step_start (px extra : Word) : step (pair (Encoding.encodeList id [px,true::extra]) []) = advance px (true::extra) [] := by simp [step]

@[simp] theorem step_next (px extra pref : Word) (n : ℕ) : step (pair (state px (true::extra) pref) (encodeNatListBin [n])) = advance px (true::extra) (pref ++ [decide (n=0)]) := by
  have h : (encodeNatListBin [n]).length ≠ 0 := by change (true :: _).length ≠ 0; simp
  simp [step,state,h]

end DetDLP.s8e


