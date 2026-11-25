-- Prove2me | Definitions.Def_DetDLP_S8A_FpPrefixStep
-- name    : DetDLP_S8A_FpPrefixStep
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:05:16.878952+00:00
-- url     : https://prove2.me/theorems/af6ca11b-4c4e-43c2-a4cb-c1aeafa3c92b
-- title:
--   Polynomial-time transition for finite-field prefix decoding
-- statement:
--   The transition parses a framed state and oracle answer, chooses the left child exactly when its count is positive, and either issues the next query or encodes the complete tuple. The valid small-plan case immediately emits the four-entry decomposition.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_M89_S1_Plans
import Definitions.Def_DetDLP_W4_M5EvalFrontend
import Definitions.Def_DetDLP_W5_M6Sort
import Definitions.Def_ToTuring_Lib_List2
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace DetDLP.m89_enum_words
open M89S1 Groundwork Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.prodMk
  Groundwork.PolyT.map Groundwork.PolyT.flatMap Groundwork.PolyT.filter Groundwork.PolyT.filterMap
  Groundwork.PolyT.mod Groundwork.PolyT.mul Groundwork.PolyT.div Groundwork.PolyT.idxOf Groundwork.PolyT.length
  P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_id__1c5d0f44cc8f
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_ite__226169acf219
  P2M_Groundwork_PolyT_some__e6a32bd6af45

abbrev Word := List Bool
abbrev State := Bool × Bool × Word × List Word
def scan (s : State) (b : Bool) : State :=
  bif s.1 then bif s.2.1 then s else (false,true,b::s.2.2.1,s.2.2.2)
  else bif s.2.1 then bif b then (true,false,s.2.2.1,s.2.2.2) else (false,false,[],s.2.2.1.reverse :: s.2.2.2)
  else bif b then (false,true,[],s.2.2.2) else (true,true,[],s.2.2.2)
def fields (w : Word) := (w.foldl scan (false,false,[],[])).2.2.2.reverse

private theorem scan_size (s : State) (b : Bool) : len (scan s b) ≤ len s + 5 := by
  obtain ⟨i,j,w,l⟩ := s; cases i <;> cases j <;> cases b <;> simp [scan,len_pair,len_bools,len_bool,len_cons,len_nil] <;> omega
@[local fun_prop] theorem fields_poly : PolyT fields := by
  have h : PolyT (fun w : Word => w.foldl scan (false,false,[],[])) := by
    refine foldl_add (g:=fun _ => scan) (by fun_prop) (by fun_prop) (by unfold scan; fun_prop) ⟨_,PB.const 5,?_⟩
    exact fun _ s e _ => scan_size s e
  unfold fields; fun_prop

private theorem scan_frame (w acc : Word) (l : List Word) : (Encoding.frame w).foldl scan (false,true,acc,l) = (false,false,[],(acc.reverse++w)::l) := by
  induction w generalizing acc with
  | nil => simp [Encoding.frame,scan]
  | cons b w ih => change (Encoding.frame w).foldl scan (false,true,b::acc,l) = _; simpa using ih (b::acc)

@[simp] theorem fields_encode (l : List Word) : fields (Encoding.encodeList id l) = l := by
  have run (L a : List Word) : (Encoding.encodeList id L).foldl scan (false,false,[],a) = (true,true,[],L.reverse++a) := by
    induction L generalizing a with
    | nil => rfl
    | cons w L ih =>
      change (Encoding.frame w ++ Encoding.encodeList id L).foldl scan (false,true,[],a) = _
      rw [List.foldl_append,scan_frame]; simpa using ih (w::a)
  simp [fields,run]

private theorem frame_flat (w : Word) : Encoding.frame w = w.flatMap (fun b => [true,b]) ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [Encoding.frame,List.flatMap] using congrArg (fun z => true::b::z) ih

@[local fun_prop] theorem enc_poly {α : Type} [Enc α] {g : α → List Word} (hg : PolyT g) : PolyT (fun x => Encoding.encodeList id (g x)) := by
  have he (l : List Word) : Encoding.encodeList id l = l.flatMap (fun u => true :: Encoding.frame u) ++ [false] := by
    induction l with
    | nil => rfl
    | cons w l ih => change true :: (Encoding.frame w ++ Encoding.encodeList id l) = _; simp [ih,List.flatMap,List.append_assoc]
  simp only [he,frame_flat]; fun_prop


def coord (w : Word) (b i : ℕ) := bval (((w.drop (i*b)).take b).reverse)

def indices (w : Word) := List.range w.length
@[local fun_prop] theorem indices_poly {α : Type} [Enc α] {f : α → Word} (hf : PolyT f) : PolyT (fun x => indices (f x)) := by
  apply Groundwork.PolyT.range
  change PolyT (fun x => List.replicate (f x).length ())
  simp only [←List.map_const (l:=(_ : Word)) (b:=())]; fun_prop


@[local fun_prop] theorem co_poly {α : Type} [Enc α] {w : α → Word} {b i : α → ℕ} (hw : PolyT w) (hb : PolyT b) (hi : PolyT i) :
    PolyT (fun x => coord (w x) (b x) (i x)) := by unfold coord; fun_prop


end DetDLP.m89_enum_words
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DetDLP.m89_decode_step
open M89S1 m89_enum_words Groundwork Groundwork.PolyT w4_M5Evaluator
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.prodMk
  Groundwork.PolyT.map Groundwork.PolyT.flatMap Groundwork.PolyT.filter Groundwork.PolyT.length Groundwork.PolyT.mul Groundwork.PolyT.div
  P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_id__1c5d0f44cc8f
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_ite__226169acf219
  fields_poly enc_poly indices_poly co_poly w5_M6Sort.decode_poly w5_M6Sort.encode_poly splitFrame_comp

def pair (s a : Word) := s.flatMap (fun b => [true,b]) ++ [false] ++ a
@[simp] theorem split_pair (s a : Word) : splitFrame (pair s a) = (s,a) := by
  have hf : ∀ x : Word, Encoding.frame x = x.flatMap (fun b => [true,b]) ++ [false] := by
    intro x; induction x with | nil => rfl | cons b x ih => simpa [Encoding.frame,List.flatMap] using congrArg (fun z => true::b::z) ih
  simpa only [pair,hf] using splitFrame_frame_append s a

@[local fun_prop] theorem pair_poly {α : Type} [Enc α] {s a : α → Word} (hs : PolyT s) (ha : PolyT a) : PolyT (fun x => pair (s x) (a x)) := by unfold pair; fun_prop

def fpFinish (b : ℕ) (w : Word) := encodeNatListBin (((indices w).filter (fun i => decide (i < w.length/b))).map (fun i => coord w b i))
@[local fun_prop] theorem finish_poly {α : Type} [Enc α] {b : α → ℕ} {w : α → Word} (hb : PolyT b) (hw : PolyT w) : PolyT (fun x => fpFinish (b x) (w x)) := by
  unfold fpFinish; apply w5_M6Sort.encode_poly; apply Groundwork.PolyT.map <;> fun_prop

def state (px plan pref : Word) := Encoding.encodeList id [px,plan,pref]

def advance (px plan pref : Word) :=
  let ns := fields px
  let extras := fields plan.tail
  let p := ns.getD 0 []
  let target := ns.getD 1 []
  let seed := extras.getD 1 []
  if pref.length < seed.length then
    false :: pair (state px plan pref) (queryWord 5 p [extras.getD 0 [],seed,target,pref ++ [false]])
  else true :: fpFinish ((bval p - 1).bits.length) pref

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
  else true :: encodeNatListBin [(w5_M6Sort.decode px).getD 1 0,1,1,1]

theorem step_poly : PolyT step := by unfold step; dsimp only; fun_prop

@[simp] theorem step_none (p x : ℕ) : step (pair (Encoding.encodeList id [encodeNatListBin [p,x],[false]]) []) = true :: encodeNatListBin [x,1,1,1] := by simp [step]

@[simp] theorem step_start (px extra : Word) : step (pair (Encoding.encodeList id [px,true::extra]) []) = advance px (true::extra) [] := by simp [step]

@[simp] theorem step_next (px extra pref : Word) (n : ℕ) : step (pair (state px (true::extra) pref) (encodeNatListBin [n])) = advance px (true::extra) (pref ++ [decide (n=0)]) := by
  have h : (encodeNatListBin [n]).length ≠ 0 := by change (true :: _).length ≠ 0; simp
  simp [step,state,h]

end DetDLP.m89_decode_step


