-- Prove2me | Definitions.Def_DetDLP_S8F_Controller
-- name    : DetDLP_S8F_Controller
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:16:34.853459+00:00
-- url     : https://prove2.me/theorems/5fbda7ca-463a-4aaf-889d-0c47dee60514
-- title:
--   Elliptic-curve Stage I plan preparation controller
-- statement:
--   A polynomial-time state transition first asks for the order of the curve, checks the general-regime condition, and performs eight moment queries per seed bit. The raw input is retained in either mode.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_S8B_Parameters
import Definitions.Def_DetDLP_S8B_MomentCompare
import Definitions.Def_DetDLP_M89_S1_Queries
import Definitions.Def_ToTuring_Lib_List2
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_foldl_add
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace DetDLP.S8F
open S8B

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


def enc (l : List Word) := Encoding.encodeList id l
def pair (w v : Word) := Encoding.frame w ++ v

theorem frame_eq (w v : Word) : pair w v = w.flatMap (fun b => [true,b]) ++ [false] ++ v := by simp [pair,frame_flat]

@[local fun_prop] theorem pair_poly {α} [Enc α] {w v : α → Word} (hw : PolyT w) (hv : PolyT v) : PolyT (fun x => pair (w x) (v x)) := by simp only [frame_eq]; fun_prop

@[local fun_prop] theorem count_poly {α} [Enc α] {f : α → ℕ} (hf : PolyT f) : PolyT (fun x => countWord (f x)) := by unfold countWord; fun_prop

def unusedFpLen (p : ℕ) := blocks (p-1).size * 2 * (p-1).size
def parameterList (p : ℕ) := ((p.bits ++ [false,false]).take (blocks (p-1).size)).map (fun _ => ())

attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f
@[local fun_prop] theorem params_poly {α} [Enc α] {p : α → ℕ} (hp : PolyT p) : PolyT (fun x => parameterList (p x)) := by
  unfold parameterList; apply Groundwork.PolyT.map (by fun_prop); apply Groundwork.PolyT.take (blocks_poly (by fun_prop)) (by fun_prop)

theorem unary_length {α} [Enc α] {l : α → List Unit} (hl : PolyT l) : Unary (fun x => (l x).length) := by
  apply hl.congr; intro x; exact List.eq_replicate_of_mem (fun a _ => Subsingleton.elim ..)

def finish (raw plan : Word) := true :: enc [raw,plan]

@[local fun_prop] theorem fields_comp {α} [Enc α] {w : α → Word} (hw : PolyT w) : PolyT (fun x => fields (w x)) := Groundwork.PolyT.comp fields_poly hw
@[local fun_prop] theorem finish_poly {α} [Enc α] {r w : α → Word} (hr : PolyT r) (hw : PolyT w) : PolyT (fun x => finish (r x) (w x)) := by unfold finish enc; fun_prop

attribute [local fun_prop] params_poly fields_comp pair_poly enc_poly count_poly finish_poly blocks_poly P2M_Groundwork_PolyT_size__c8c8eb1b342f
def stageT (p g : ℕ) := threshold p (g-1) (parameterList p).length g
@[local fun_prop] theorem stageT_poly {α} [Enc α] {p g : α → ℕ} (hp : PolyT p) (hg : PolyT g) : PolyT (fun x => stageT (p x) (g x)) := by
  apply threshold_poly hp (by fun_prop) (by fun_prop) (unary_length (params_poly hp)) (by fun_prop)

def select (p g : ℕ) (vs : List Word) :=
  let m := (parameterList p).length; let t := stageT p g
  let v := fun i => bval (vs.getD i [])
  momentRight (p^m) (((g-1)*t)^m) g (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)

@[local fun_prop] theorem select_poly {α} [Enc α] {p g : α → ℕ} {vs : α → List Word} (hp : PolyT p) (hg : PolyT g) (hv : PolyT vs) : PolyT (fun x => select (p x) (g x) (vs x)) := by
  unfold select; dsimp only; apply momentRight_poly
  · exact pow_unary hp (unary_length (params_poly hp))
  · exact pow_unary (by fun_prop) (unary_length (params_poly hp))
  all_goals fun_prop

def curve (t : Bool) (raw : Word) := if t then (fields raw).getD 0 [] else raw
def prime (c : Word) := bval ((fields c).getD 0 [])
def seedLen (p : ℕ) := blocks (p-1).size * 4 * (p-1).size
@[local fun_prop] theorem curve_poly {α} [Enc α] (t : Bool) {r : α → Word} (hr : PolyT r) : PolyT (fun x => curve t (r x)) := by cases t <;> simp [curve] <;> fun_prop
@[local fun_prop] theorem prime_poly {α} [Enc α] {r : α → Word} (hr : PolyT r) : PolyT (fun x => prime (r x)) := by unfold prime; fun_prop
def ask (raw c : Word) (p g : ℕ) (w : Word) (vs : List Word) : Word :=
  let i := vs.length
  false :: pair (enc (raw :: countWord g :: w :: vs)) (queryWord 2 c [countWord (i%4),countWord (stageT p g), w++[decide (4 ≤ i)]])

def init (raw c : Word) (p g : ℕ) := if 64 ≤ g ∧ 4096*blocks (p-1).size ≤ g-1 then ask raw c p g [] [] else finish raw [false]
def advance (raw c : Word) (p g : ℕ) (newW : Word) := if seedLen p ≤ newW.length then finish raw (true :: enc [countWord (stageT p g),newW]) else ask raw c p g newW []
def driver (raw c : Word) (p g : ℕ) (w : Word) (vs : List Word) := if vs.length < 8 then ask raw c p g w vs else advance raw c p g (w ++ [select p g vs])
def resume (t : Bool) (state : List Word) (ans : Word) :=
  let r := state.getD 0 []; let c := curve t r; let p := prime c
  if state.length ≤ 1 then init r c p (bval ans) else
    driver r c p (bval (state.getD 1 [])) (state.getD 2 []) (state.drop 3 ++ [ans])
def orderAsk (t : Bool) (r : Word) := false :: pair (enc [r]) (queryWord 0 (curve t r) [])
def outerStep (t : Bool) (outer : List Word) := let st := outer.getD 0 []; if outer.length ≤ 1 then orderAsk t st else resume t (fields st) (outer.getD 1 [])
def step (t : Bool) (a : Word) := outerStep t (fields (true :: (a ++ [false])))
@[local fun_prop] theorem ask_poly {α} [Enc α] {raw c w : α → Word} {p g : α → ℕ} {vs : α → List Word} (hr : PolyT raw) (hc : PolyT c) (hp : PolyT p) (hg : PolyT g) (hw : PolyT w) (hv : PolyT vs) : PolyT (fun x => ask (raw x) (c x) (p x) (g x) (w x) (vs x)) := by unfold ask enc queryWord; dsimp only; fun_prop
@[local fun_prop] theorem init_poly {α} [Enc α] {r c : α → Word} {p g : α → ℕ} (hr : PolyT r) (hc : PolyT c) (hp : PolyT p) (hg : PolyT g) : PolyT (fun x => init (r x) (c x) (p x) (g x)) := by
  have hn : PolyT (fun x => p x - 1) := Groundwork.PolyT.sub hp (const 1)
  have hm : PolyT (fun x => blocks (p x - 1).size) := blocks_poly (P2M_Groundwork_PolyT_size__c8c8eb1b342f hn)
  have hc0 := Groundwork.PolyT.decide_le (const (α:=α) 64) hg
  have hc1 := Groundwork.PolyT.decide_le (Groundwork.PolyT.mul (const 4096) hm) (Groundwork.PolyT.sub hg (const 1))
  have hA := ask_poly hr hc hp hg (const ([]:Word)) (const ([]:List Word))
  have hF := finish_poly hr (const [false])
  unfold init; simp only [ite_and]; exact P2M_Groundwork_PolyT_ite__226169acf219 hc0 (P2M_Groundwork_PolyT_ite__226169acf219 hc1 hA hF) hF
@[local fun_prop] theorem advance_poly {α} [Enc α] {r c w : α → Word} {p g : α → ℕ} (hr : PolyT r) (hc : PolyT c) (hp : PolyT p) (hg : PolyT g) (hw : PolyT w) : PolyT (fun x => advance (r x) (c x) (p x) (g x) (w x)) := by unfold advance enc seedLen; fun_prop
@[local fun_prop] theorem driver_poly {α} [Enc α] {r c w : α → Word} {p g : α → ℕ} {vs : α → List Word} (hr : PolyT r) (hc : PolyT c) (hp : PolyT p) (hg : PolyT g) (hw : PolyT w) (hv : PolyT vs) : PolyT (fun x => driver (r x) (c x) (p x) (g x) (w x) (vs x)) := by unfold driver; fun_prop
@[local fun_prop] theorem resume_poly {α} [Enc α] (t : Bool) {s : α → List Word} {a : α → Word} (hs : PolyT s) (ha : PolyT a) : PolyT (fun x => resume t (s x) (a x)) := by unfold resume; dsimp only; fun_prop
@[local fun_prop] theorem order_poly {α} [Enc α] (t : Bool) {r : α → Word} (hr : PolyT r) : PolyT (fun x => orderAsk t (r x)) := by unfold orderAsk enc queryWord; fun_prop
@[local fun_prop] theorem outerStep_poly {α} [Enc α] (t : Bool) {s : α → List Word} (hs : PolyT s) : PolyT (fun x => outerStep t (s x)) := by unfold outerStep; dsimp only; fun_prop
theorem step_poly (t : Bool) : PolyT (step t) := by change PolyT (fun w : Word => outerStep t (fields (true::(w++[false])))); fun_prop
end DetDLP.S8F


