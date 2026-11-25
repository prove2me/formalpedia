-- Prove2me | Definitions.Def_DetDLP_D4BEntryCodec
-- name    : DetDLP_D4BEntryCodec
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:19:12.937145+00:00
-- url     : https://prove2.me/theorems/ea2f9803-c8eb-49b1-b2eb-71d3953795d3
-- title:
--   Source descriptor selection for residual digit entries
-- statement:
--   Decode the framed list of source descriptors in a residual branch, select the descriptor of the queried vertex, and retain its original vertex index and port assignment. The selector acts in polynomial time on bit words.

import Definitions.Def_DetDLP_D4Plan
import Definitions.Def_DetDLP_D4Slice

set_option autoImplicit false
namespace DetDLP.D4BEntry
open Groundwork DetDLP_W1_Queries D4Plan D4Slice AppendixD4 ResidualScalarOracle
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Groundwork.PolyT
abbrev W := List Bool
attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.map
  PolyT.flatMap PolyT.length PolyT.div PolyT.mod PolyT.zip
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_ite__226169acf219
  D4Slice.field_poly DetDLP_W1_Queries.frame_poly w5_M6Sort.decode_poly w5_M6Sort.encode_poly

def listWord (xs : List W) := xs.flatMap (fun w => true :: DetDLP_W1_Queries.frame w) ++ [false]
@[simp] theorem listWord_eq (xs : List W) : listWord xs = Encoding.encodeList id xs := by
  induction xs with
  | nil => rfl
  | cons w ws ih => simpa [listWord, Encoding.encodeList,List.append_assoc] using congrArg (fun a => true :: (Encoding.frame w ++ a)) ih
@[local fun_prop] theorem listWord_poly {α : Type} [Enc α] {xs : α → List W} (hx : PolyT xs) : PolyT fun a => listWord (xs a) := by
  unfold listWord; apply PolyT.append; apply PolyT.flatMap (f := fun _ w => true :: DetDLP_W1_Queries.frame w); fun_prop; exact hx; fun_prop

def atomStep (s : Bool × Bool × W × List W) (b : Bool) : Bool × Bool × W × List W :=
  bif s.1 then bif s.2.1 then s else (false,true,b :: s.2.2.1,s.2.2.2)
  else bif s.2.1 then bif b then (true,false,s.2.2.1,s.2.2.2)
    else (false,false,[],s.2.2.1.reverse :: s.2.2.2)
  else bif b then (false,true,[],s.2.2.2) else (true,true,[],s.2.2.2)
def atoms (w : W) : List W := (w.foldl atomStep (false,false,[],[])).2.2.2.reverse
@[local fun_prop] theorem atoms_poly : PolyT atoms := by
  have hp : PolyT fun w : W => w.foldl atomStep (false,false,[],[]) := by
    apply foldl_add (g := fun _ => atomStep) (by fun_prop) (by fun_prop) (by unfold atomStep; fun_prop)
    refine ⟨fun _ => 8, PB.const 8, ?_⟩
    intro _ s b _; obtain ⟨i,j,w,ws⟩ := s
    cases i <;> cases j <;> cases b <;> simp [atomStep,len_pair,len_bools,len_bool,len_cons,len_nil] <;> omega
  unfold atoms; fun_prop
private theorem atom_frame (w rev : W) (ws : List W) :
    (Encoding.frame w).foldl atomStep (false,true,rev,ws) = (false,false,[],(rev.reverse ++ w) :: ws) := by
  induction w generalizing rev with
  | nil => simp [Encoding.frame,atomStep]
  | cons b w ih => change (Encoding.frame w).foldl atomStep (false,true,b::rev,ws) = _; simpa using ih (b::rev)
private theorem atom_scan (xs ws : List W) : (Encoding.encodeList id xs).foldl atomStep (false,false,[],ws) = (true,true,[],xs.reverse ++ ws) := by
  induction xs generalizing ws with
  | nil => rfl
  | cons x xs ih => change (Encoding.frame x ++ Encoding.encodeList id xs).foldl atomStep (false,true,[],ws) = _; rw [List.foldl_append,atom_frame]; simpa using ih (x::ws)
@[simp] theorem atoms_list (xs : List W) : atoms (Encoding.encodeList id xs) = xs := by simp [atoms,atom_scan]

def sourceQuery (w : W) :=
  let src := (atoms (field 2 (field 2 (field 0 w)))).getD (bval (field 1 w)) []
  listWord [src, field 1 w, field 2 w]

theorem sourceQuery_poly : PolyT sourceQuery := by unfold sourceQuery; fun_prop

@[simp] theorem field_cons (n : ℕ) (x : W) (xs : List W) : field (n+1) (Encoding.encodeList id (x::xs)) = field n (Encoding.encodeList id xs) := by simp [field]
@[simp] theorem field_zero (x : W) (xs : List W) : field 0 (Encoding.encodeList id (x::xs)) = x := by simp [field]
@[simp] theorem sourceQuery_spec {C c : ℕ} {x : Input C c} (P : Plan x) (u : Fin P.N)
    (a : Fin (P.R u).nV → Fin (J P u)) (v : Fin (P.R u).nV) (t : Fin ((P.R u).deg v) → Bool) :
    sourceQuery (encodePortQuery (digitDesc P u a) v.val (List.ofFn t)) = encodePortQuery (P.source u v) v.val (List.ofFn t) := by
  simp [sourceQuery, digitDesc, branch, encodePortQuery, List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt]
end DetDLP.D4BEntry


