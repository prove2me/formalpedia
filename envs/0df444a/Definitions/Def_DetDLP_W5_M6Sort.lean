-- Prove2me | Definitions.Def_DetDLP_W5_M6Sort
-- name    : DetDLP_W5_M6Sort
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T00:27:17.384548+00:00
-- url     : https://prove2.me/theorems/1a9b5d4e-5ab1-47a2-a87e-d7c7910e9a08
-- title:
--   M6 Sort
-- statement:
--   A polynomial-time word postprocessor parses a binary list of natural numbers, sorts its elements and re-encodes them canonically.

import Definitions.Def_DetDLP_PolyTBridge
import Definitions.Def_ToTuring_Lib_Nat1
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_flatMap

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace DetDLP.w5_M6Sort
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Groundwork Groundwork.PolyT
attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.fst
  Groundwork.PolyT.snd Groundwork.PolyT.prodMk Groundwork.PolyT.flatMap Groundwork.PolyT.filter
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_cons__3a60f43a3b86
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219

abbrev State := Bool × Bool × List Bool × List ℕ

def scan (s : State) (b : Bool) : State :=
  bif s.1 then bif s.2.1 then s else (false,true,b :: s.2.2.1,s.2.2.2)
  else bif s.2.1 then bif b then (true,false,s.2.2.1,s.2.2.2)
    else (false,false,[],bval s.2.2.1.reverse :: s.2.2.2)
  else bif b then (false,true,[],s.2.2.2) else (true,true,[],s.2.2.2)

def decode (w : List Bool) : List ℕ := (w.foldl scan (false,false,[],[])).2.2.2.reverse

private theorem scan_size (s : State) (b : Bool) : len (scan s b) ≤ len s + 4 := by
  obtain ⟨k,j,w,l⟩ := s
  have h : (bval w.reverse).size ≤ w.length := Nat.size_le.mpr (by simpa using bval_lt w.reverse)
  cases k <;> cases j <;> cases b <;> simp [scan,len_pair,len_bools,len_bool,len_nat,len_cons,len_nil] <;> omega

@[local fun_prop] theorem decode_poly : PolyT decode := by
  have h : PolyT fun w : List Bool => w.foldl scan (false,false,[],[]) := by
    refine foldl_add (g := fun _ => scan) (by fun_prop) (by fun_prop) (by unfold scan; fun_prop) ?_
    exact ⟨fun _ => 4, PB.const 4, fun _ s e _ => scan_size s e⟩
  unfold decode; fun_prop

private theorem frame_scan (u rev : List Bool) (l : List ℕ) :
    (Encoding.frame u).foldl scan (false,true,rev,l) =
      (false,false,[],bval (rev.reverse ++ u) :: l) := by
  induction u generalizing rev with
  | nil => simp [Encoding.frame,scan]
  | cons b u ih =>
    change (Encoding.frame u).foldl scan (false,true,b::rev,l) = _
    simpa using ih (b::rev)

private theorem decode_scan (ns l : List ℕ) :
    (encodeNatListBin ns).foldl scan (false,false,[],l) = (true,true,[],ns.reverse ++ l) := by
  induction ns generalizing l with
  | nil => rfl
  | cons n ns ih =>
    change (Encoding.frame (countWord n) ++ encodeNatListBin ns).foldl scan (false,true,[],l) = _
    have hv : bval (countWord n) = n := by by_cases hn : n = 0; subst n; rfl; simp [countWord,hn,bval_bits]
    rw [List.foldl_append,frame_scan]; simpa [hv] using ih (n::l)

@[simp] theorem decode_encode (ns : List ℕ) : decode (encodeNatListBin ns) = ns := by
  simp [decode,decode_scan]

def insert (l : List ℕ) (n : ℕ) := l.filter (· < n) ++ n :: l.filter (n ≤ ·)

def sort (l : List ℕ) := l.foldl insert []

private theorem partition_perm (l : List ℕ) (n : ℕ) :
    (l.filter (· < n) ++ l.filter (n ≤ ·)).Perm l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : a < n
    · simpa [h, Nat.not_le.mpr h] using ih.cons a
    · simp only [List.filter_cons, decide_eq_true_eq, h, Nat.le_of_not_lt h,if_false,if_true]
      exact (List.perm_middle ..).trans (ih.cons a)

private theorem insert_perm (l : List ℕ) (n : ℕ) : (insert l n).Perm (n :: l) :=
  (List.perm_middle ..).trans ((partition_perm l n).cons n)

private theorem len_perm {l r : List ℕ} (p : l.Perm r) : len l = len r := by
  induction p with
  | nil => rfl
  | cons a _ ih => simp [len_cons,ih]
  | swap => simp [len_cons]; omega
  | trans _ _ i j => exact i.trans j

private theorem insert_sorted {l : List ℕ} (h : l.Pairwise (· ≤ ·)) (n : ℕ) :
    (insert l n).Pairwise (· ≤ ·) := by
  apply List.pairwise_append.mpr
  refine ⟨h.filter _, List.pairwise_cons.mpr ⟨?_,h.filter _⟩,?_⟩
  · intro a ha; simpa using (List.mem_filter.mp ha).2
  · intro a ha b hb
    have h₁ : a < n := by simpa using (List.mem_filter.mp ha).2
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h₁.le
    · exact h₁.le.trans (by simpa using (List.mem_filter.mp hb).2)

private theorem sorted_fold (l acc : List ℕ) (h : acc.Pairwise (· ≤ ·)) :
    (l.foldl insert acc).Pairwise (· ≤ ·) ∧ (l.foldl insert acc).Perm (l.reverse ++ acc) := by
  induction l generalizing acc with
  | nil => simpa using h
  | cons a l ih =>
    obtain ⟨s,p⟩ := ih (insert acc a) (insert_sorted h a)
    exact ⟨s, by simpa using p.trans ((insert_perm acc a).append_left l.reverse)⟩

theorem sort_eq (l : List ℕ) : sort l = l.mergeSort := by
  obtain ⟨s,p⟩ := sorted_fold l [] (by simp)
  have hp : (sort l).Perm l := (by simpa [sort] using p : (sort l).Perm l.reverse) |>.trans (List.reverse_perm _)
  apply List.Perm.eq_of_pairwise' s _ (hp.trans (List.mergeSort_perm l _).symm)
  simpa using List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b)) (by grind) (by grind) l

@[local fun_prop] theorem sort_poly : PolyT sort := by
  unfold sort
  refine foldl_add (g := fun _ => insert) (by fun_prop) (by fun_prop) (by unfold insert; fun_prop) ?_
  refine ⟨fun n => n+2, PB.id'.add (PB.const 2), ?_⟩
  intro l s a ha; rw [len_perm (insert_perm s a),len_cons]; have := len_le_of_mem ha; dsimp only; omega

@[local fun_prop] theorem cw_poly {α : Type} [Enc α] {f : α → ℕ} (h : PolyT f) :
    PolyT (fun x => countWord (f x)) := by unfold countWord; fun_prop

private theorem frame_flat (w : List Bool) : Encoding.frame w = w.flatMap (fun b => [true,b]) ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [Encoding.frame, List.flatMap] using congrArg (fun u => true::b::u) ih

private theorem encode_flat (ns : List ℕ) : encodeNatListBin ns =
    ns.flatMap (fun n => true :: Encoding.frame (countWord n)) ++ [false] := by
  induction ns with
  | nil => rfl
  | cons n ns ih => change true :: (Encoding.frame (countWord n) ++ encodeNatListBin ns) = _
                    rw [ih]; simp [List.flatMap, List.append_assoc]

@[local fun_prop] theorem encode_poly {α : Type} [Enc α] {f : α → List ℕ} (h : PolyT f) :
    PolyT (fun x => encodeNatListBin (f x)) := by
  simp only [encode_flat, frame_flat]; fun_prop

theorem machine : ∃ (M : Computation.PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ), ∀ ns : List ℕ,
    RunsWithin M out (encodeNatListBin ns) (encodeNatListBin ns.mergeSort)
      (polyBound K (encodeNatListBin ns).length) (polyBound K (encodeNatListBin ns).length) := by
  have hp : PolyT (fun w => encodeNatListBin (sort (decode w))) := encode_poly (sort_poly.comp decode_poly)
  obtain ⟨M,o,K,h⟩ := PolyTBridge.polyT_listBool_runsWithin _ hp
  exact ⟨M,o,K,fun l => by simpa [sort_eq] using h (encodeNatListBin l)⟩

end DetDLP.w5_M6Sort


