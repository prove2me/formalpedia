-- Prove2me | Definitions.Def_DetDLP_M6_DFSOracleStep
-- name    : DetDLP_M6_DFSOracleStep
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:24:47.001803+00:00
-- url     : https://prove2.me/theorems/894d08a4-f0b1-4005-a300-53dad1f0c602
-- title:
--   Factor-splitting DFS oracle packet transition
-- statement:
--   Encode and decode a depth-first work stack and accumulated leaves. Each polynomial-time transition either queries the divisor machine at the next pending node or sorts and returns the finished leaves.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proposition 2.6 (pp. 10–11)

import Definitions.Def_DetDLP_W5_M6Sort
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_mod

set_option autoImplicit false
namespace DetDLP.M6Loop
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Groundwork Groundwork.PolyT
attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.div PolyT.mod
  PolyT.flatMap PolyT.length P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_cons__3a60f43a3b86
  w5_M6Sort.cw_poly w5_M6Sort.decode_poly w5_M6Sort.encode_poly w5_M6Sort.sort_poly
abbrev W := List Bool
def pair (a b : W) := a.flatMap (fun v => [true,v]) ++ [false] ++ b
@[local fun_prop] theorem pair_poly {α : Type} [Enc α] {a b : α → W} (ha : PolyT a) (hb : PolyT b) : PolyT (fun i => pair (a i) (b i)) := by unfold pair; fun_prop
abbrev Scan := Bool × Bool × W × W
def scan (s : Scan) (b : Bool) : Scan :=
  bif s.1 then (true,false,s.2.2.1,b::s.2.2.2) else
  bif s.2.1 then (false,false,b::s.2.2.1,s.2.2.2) else (!b,b,s.2.2.1,s.2.2.2)
def unpack (w : W) : W × W := let s := w.foldl scan (false,false,[],[]); (s.2.2.1.reverse,s.2.2.2.reverse)
@[local fun_prop] theorem unpack_poly : PolyT unpack := by
  have h : PolyT (fun w : W => w.foldl scan (false,false,[],[])) := by
    refine foldl_add (g := fun _ => scan) (by fun_prop) (by fun_prop) (by unfold scan; fun_prop) ⟨fun _ => 4, PB.const 4, ?_⟩
    intro _ s b _; obtain ⟨j,k,x,y⟩ := s
    cases j <;> cases k <;> cases b <;> simp [scan,len_pair,len_bool,len_bools] <;> omega
  unfold unpack; fun_prop
private theorem scan_left (a u : W) : (a.flatMap (fun v => [true,v])).foldl scan (false,false,u,[]) = (false,false,a.reverse ++ u,[]) := by
  induction a generalizing u with
  | nil => simp
  | cons b a ih => change (a.flatMap _).foldl scan (false,false,b::u,[]) = _; simpa using ih (b::u)
private theorem scan_right (b u v : W) : b.foldl scan (true,false,u,v) = (true,false,u,b.reverse ++ v) := by
  induction b generalizing v with
  | nil => simp
  | cons x b ih => change b.foldl scan (true,false,u,x::v) = _; simpa using ih (x::v)
@[simp] theorem unpack_pair (a b : W) : unpack (pair a b) = (a,b) := by simp [unpack,pair,List.foldl_append,scan_left,scan,scan_right]
def state (todo acc : List ℕ) := pair (encodeNatListBin todo) (encodeNatListBin acc)
def dispatch (todo acc : List ℕ) : W :=
  if todo.isEmpty then true :: encodeNatListBin (w5_M6Sort.sort acc.reverse)
  else false :: pair (state todo acc) (countWord (todo.tail.headD 0))
@[local fun_prop] theorem dispatch_poly {α : Type} [Enc α] {t a : α → List ℕ} (ht : PolyT t) (ha : PolyT a) : PolyT (fun z => dispatch (t z) (a z)) := by unfold dispatch state; fun_prop

def advance (t a : List ℕ) (d : ℕ) : W :=
  let k := t.headD 0; let x := t.tail.headD 0; let rest := t.tail.tail
  if 0 < k ∧ 2 ≤ d ∧ d < x ∧ x % d = 0 then dispatch ((k-1)::d::(k-1)::(x/d)::rest) a
  else dispatch rest (x::a)
@[local fun_prop] theorem advance_poly {α : Type} [Enc α] {t a : α → List ℕ} {d : α → ℕ} (ht : PolyT t) (ha : PolyT a) (hd : PolyT d) : PolyT (fun z => advance (t z) (a z) (d z)) := by unfold advance; fun_prop

def step (w : W) : W :=
  let q := unpack w
  if q.2.isEmpty then dispatch [q.1.length,bval q.1] []
  else let s := unpack q.1; advance (w5_M6Sort.decode s.1) (w5_M6Sort.decode s.2) (bval q.2)
theorem step_poly : PolyT step := by unfold step; fun_prop
@[simp] theorem value_cw (x : ℕ) : bval (countWord x) = x := by by_cases h : x=0; subst x; rfl; simp [countWord,h,bval_bits]
@[simp] theorem empty_cw (x : ℕ) : (countWord x).isEmpty = false := by
  by_cases h : x=0
  · subst x; rfl
  · simp only [countWord,if_neg h,List.isEmpty_eq_false_iff]; intro he
    have hv := bval_bits x; rw [he] at hv; exact h hv.symm
@[simp] theorem next_eq (t a : List ℕ) (d : ℕ) : step (pair (state t a) (countWord d)) = advance t a d := by simp [step,state]
end DetDLP.M6Loop


