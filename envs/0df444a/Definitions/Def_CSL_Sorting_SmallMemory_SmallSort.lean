-- Prove2me | Definitions.Def_CSL_Sorting_SmallMemory_SmallSort
-- name    : CSL_Sorting_SmallMemory_SmallSort
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:40:01.826171+00:00
-- url     : https://prove2.me/theorems/ac2f2e0a-6635-41c4-987b-4c743a14736d
-- title:
--   Coded sorting library: Sorting / SmallMemory / SmallSort
-- statement:
--   Module `CodedSorting.Sorting.SmallMemory.SmallSort` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Two physical block buffers simulate the two-word machine. Each virtual
--   word is stored in the first cell of its own physical block. All operations
--   below read or write whole blocks. The remaining cells contain padding; the
--   simulation does not treat a disk access as a free resident operation.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.SmallMemory.SmallSort

import Definitions.Def_CSL_Compat
import Mathlib.Data.List.Sort
import Definitions.Def_CSL_Sorting_SmallMemory_Uniform_RadixSort

section BlockLift
/-! Two physical block buffers simulate the two-word machine. Each virtual
word is stored in the first cell of its own physical block. All operations
below read or write whole blocks. The remaining cells contain padding; the
simulation does not treat a disk access as a free resident operation. -/
set_option autoImplicit false
namespace CSL.TwoWordBlockLift
open TwoWordPhysicalAddresses TwoWordUniformLoop
variable {B : ℕ} {W : Type*} [DecidableEq W]

abbrev Buffer (B : ℕ) (W : Type*) := Fin B → W
structure State (B : ℕ) (W : Type*) where
  left : Buffer B W
  right : Buffer B W
  disk : ℕ → Buffer B W

inductive Command (B : ℕ) (W : Type*) where
  | readLeft (address : ℕ)
  | readRight (address : Buffer B W × Buffer B W → ℕ)
  | writeLeft (address : ℕ)
  | writeRight (address : Buffer B W × Buffer B W → ℕ)
  | cpu (f : Buffer B W × Buffer B W → Buffer B W × Buffer B W)

def step (cmd : Command B W) (s : State B W) : State B W :=
  match cmd with
  | .readLeft a => {s with left := s.disk a}
  | .readRight a => {s with right := s.disk (a (s.left,s.right))}
  | .writeLeft a => {s with disk := Function.update s.disk a s.left}
  | .writeRight a => {s with disk := Function.update s.disk (a (s.left,s.right)) s.right}
  | .cpu f => {s with left := (f (s.left,s.right)).1, right := (f (s.left,s.right)).2}

def cost : Command B W → ℕ
  | .cpu _ => 0
  | _ => 1
def execute : List (Command B W) → State B W → State B W
  | [],s => s
  | cmd::rest,s => execute rest (step cmd s)
def transfers : List (Command B W) → ℕ
  | [] => 0
  | cmd::rest => cost cmd+transfers rest

def observe (hB : 0<B) (base : ℕ) (s : State B W) : TwoWordPhysicalAddresses.State W :=
  ⟨s.left ⟨0,hB⟩,s.right ⟨0,hB⟩,fun a => s.disk (base+a) ⟨0,hB⟩⟩

def compile (hB : 0<B) (base : ℕ) : TwoWordPhysicalAddresses.Command W → Command B W
  | .readLeft a => .readLeft (base+a)
  | .readRight a => .readRight (fun _ => base+a)
  | .readRightAt a => .readRight (fun r => base+a (r.1 ⟨0,hB⟩,r.2 ⟨0,hB⟩))
  | .writeLeft a => .writeLeft (base+a)
  | .writeRight a => .writeRight (fun r => base+a (r.1 ⟨0,hB⟩,r.2 ⟨0,hB⟩))
  | .localOp f => .cpu (fun r =>
      let v := f (r.1 ⟨0,hB⟩,r.2 ⟨0,hB⟩)
      (fun _ => v.1,fun _ => v.2))

theorem update_observe (hB : 0<B) (base a : ℕ)
    (disk : ℕ → Buffer B W) (value : Buffer B W) :
    (fun b => (Function.update disk (base+a) value) (base+b) ⟨0,hB⟩)=
      Function.update (fun b => disk (base+b) ⟨0,hB⟩) a (value ⟨0,hB⟩) := by
  funext b
  by_cases h : b=a
  · subst b; simp
  · have h' : base+b≠base+a := by omega
    simp [Function.update_of_ne,h,h']

theorem step_observe (hB : 0<B) (base : ℕ)
    (cmd : TwoWordPhysicalAddresses.Command W) (s : State B W) :
    observe hB base (step (compile hB base cmd) s)=
      TwoWordPhysicalAddresses.step cmd (observe hB base s) := by
  cases cmd <;> simp [observe,step,compile,TwoWordPhysicalAddresses.step,update_observe]

theorem compile_cost (hB : 0<B) (base : ℕ)
    (cmd : TwoWordPhysicalAddresses.Command W) :
    cost (compile hB base cmd)=TwoWordPhysicalAddresses.cost cmd := by
  cases cmd <;> rfl

theorem execute_observe (hB : 0<B) (base : ℕ)
    (code : List (TwoWordPhysicalAddresses.Command W)) (s : State B W) :
    observe hB base (execute (code.map (compile hB base)) s)=
      TwoWordPhysicalAddresses.execute code (observe hB base s) := by
  induction code generalizing s with
  | nil => rfl
  | cons cmd rest ih =>
    simp only [List.map_cons,execute,TwoWordPhysicalAddresses.execute,ih,step_observe]

theorem transfers_compile (hB : 0<B) (base : ℕ)
    (code : List (TwoWordPhysicalAddresses.Command W)) :
    transfers (code.map (compile hB base))=TwoWordPhysicalAddresses.transfers code := by
  induction code with
  | nil => rfl
  | cons cmd rest ih => simp only [List.map_cons,transfers,compile_cost,ih,
      TwoWordPhysicalAddresses.transfers]

def check (base : ℕ) (p : Physical.Program W) (s : State B W) :=
  step (.readLeft (base+p.pcAddress)) s
def next (hB : 0<B) (base : ℕ) (p : Physical.Program W) (s : State B W) :=
  execute (p.body.map (compile hB base)) (check base p s)

theorem check_observe (hB : 0<B) (base : ℕ) (p : Physical.Program W) (s : State B W) :
    observe hB base (check base p s)=Physical.check p (observe hB base s) := rfl
theorem next_observe (hB : 0<B) (base : ℕ) (p : Physical.Program W) (s : State B W) :
    observe hB base (next hB base p s)=Physical.next p (observe hB base s) :=
  execute_observe hB base p.body (check base p s)

inductive LoopExecutes (hB : 0<B) (base : ℕ) (p : Physical.Program W) :
    State B W → State B W → ℕ → Prop where
  | stop (s : State B W) (h : (check base p s).left ⟨0,hB⟩=p.halt) :
      LoopExecutes hB base p s (check base p s) 1
  | more (s t : State B W) (c : ℕ)
      (h : (check base p s).left ⟨0,hB⟩≠p.halt)
      (rest : LoopExecutes hB base p (next hB base p s) t c) :
      LoopExecutes hB base p s t (1+transfers (p.body.map (compile hB base))+c)

theorem lift_loop (hB : 0<B) (base : ℕ) (p : Physical.Program W)
    {a t : TwoWordPhysicalAddresses.State W} {c : ℕ}
    (h : Physical.Executes p a t c) (s : State B W) (hs : observe hB base s=a) :
    ∃ u, LoopExecutes hB base p s u c ∧ observe hB base u=t := by
  induction h generalizing s with
  | stop a ha =>
    refine ⟨check base p s,.stop s ?_,?_⟩
    · change (Physical.check p (observe hB base s)).left=p.halt
      simpa only [hs] using ha
    · rw [check_observe,hs]
  | more a t c ha rest ih =>
    obtain ⟨u,hu,he⟩ := ih (next hB base p s) (by rw [next_observe,hs])
    refine ⟨u,?_,he⟩
    have hc : (check base p s).left ⟨0,hB⟩≠p.halt := by
      change (Physical.check p (observe hB base s)).left≠p.halt
      first
      | exact ha
      | (have h_sx := ha; simp only [hs] at h_sx ⊢; exact h_sx)
      | (have h_sx := ha; simp only [hs] at h_sx; exact h_sx)
      | (simp only [hs]; exact ha)
    simpa only [transfers_compile] using LoopExecutes.more s u c hc hu

inductive Executes (hB : 0<B) (base : ℕ) :
    List (TwoWordRadixPreparedBuild.Stage W) → State B W → State B W → ℕ → Prop where
  | done (s : State B W) : Executes hB base [] s s 0
  | straight (code : List (TwoWordPhysicalAddresses.Command W))
      (rest : List (TwoWordRadixPreparedBuild.Stage W)) (s t : State B W) (c : ℕ)
      (tail : Executes hB base rest (execute (code.map (compile hB base)) s) t c) :
      Executes hB base (.straight code::rest) s t (transfers (code.map (compile hB base))+c)
  | loop (p : Physical.Program W) (rest : List (TwoWordRadixPreparedBuild.Stage W))
      (s mid t : State B W) (ca cb : ℕ) (first : LoopExecutes hB base p s mid ca)
      (tail : Executes hB base rest mid t cb) :
      Executes hB base (.loop p::rest) s t (ca+cb)

theorem lift_stages (hB : 0<B) (base : ℕ)
    {code : List (TwoWordRadixPreparedBuild.Stage W)}
    {a t : TwoWordPhysicalAddresses.State W} {c : ℕ}
    (h : TwoWordRadixPreparedBuild.Executes code a t c)
    (s : State B W) (hs : observe hB base s=a) :
    ∃ u, Executes hB base code s u c ∧ observe hB base u=t := by
  induction h generalizing s with
  | done a => exact ⟨s,.done s,hs⟩
  | straight code rest a t c tail ih =>
    obtain ⟨u,hu,he⟩ := ih (execute (code.map (compile hB base)) s)
      (by rw [execute_observe,hs])
    refine ⟨u,?_,he⟩
    simpa only [transfers_compile] using Executes.straight code rest s u c hu
  | loop p rest a mid t ca cb first tail ih =>
    obtain ⟨v,hv,hve⟩ := lift_loop hB base p first s hs
    obtain ⟨u,hu,hue⟩ := ih v hve
    exact ⟨u,.loop p rest s v u ca cb hv hu,hue⟩

/-- Every state has exactly two physical buffers, with no extra resident
word or data-dependent mathematical counter. -/
theorem resident_card : Fintype.card (Fin B ⊕ Fin B)=2*B := by simp; omega

end CSL.TwoWordBlockLift
end BlockLift

section SmallSort
/-! A genuine two-resident-word comparison network for bounded inputs.
The program is generated from the public length only. Four transfers per
comparator sort at most eight records in at most 32 N transfers. Arbitrary
initial resident words and unrelated disk contents are permitted. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CSL.TwoWordSmallSort
open TwoWordPhysicalAddresses TwoWordRadixPreparedBuild
open TwoWordRadixInsert (Word)
variable {W : Type*} [LinearOrder W]

def FileAt (s : State W) (base : ℕ) (xs : List W) : Prop :=
  ∀ j : Fin xs.length,s.disk (base+j.val)=xs.get j

abbrev File {w : ℕ} (s : State (Word w)) (xs : List (Word w)) : Prop := FileAt s 5 xs

omit [LinearOrder W] in
theorem file_cons (s : State W) (base : ℕ) (x : W) (xs : List W) :
    FileAt s base (x::xs) ↔ s.disk base=x ∧ FileAt s (base+1) xs := by
  constructor
  · intro h
    refine ⟨by simpa using h ⟨0,by simp⟩,?_⟩
    intro j
    first
    | exact h j.succ
    | (have h_sx := h j.succ; simp only [List.get_cons_succ,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1] at h_sx ⊢; exact h_sx)
    | (have h_sx := h j.succ; simp only [List.get_cons_succ,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1] at h_sx; exact h_sx)
    | (simp only [List.get_cons_succ,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1]; exact h j.succ)
  · rintro ⟨hx,hxs⟩ j
    refine Fin.cases ?_ (fun k=>?_) j
    · simpa using hx
    · first
      | exact hxs k
      | (have h_sx := hxs k; simp only [List.get_cons_succ,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1] at h_sx ⊢; exact h_sx)
      | (have h_sx := hxs k; simp only [List.get_cons_succ,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1] at h_sx; exact h_sx)
      | (simp only [List.get_cons_succ,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1]; exact hxs k)

omit [LinearOrder W] in
theorem execute_append (a b : List (Command W)) (s : State W) :
    execute (a++b) s=execute b (execute a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons c cs ih => simpa only [List.cons_append,execute] using ih (step c s)

omit [LinearOrder W] in
theorem transfers_append (a b : List (Command W)) :
    transfers (a++b)=transfers a+transfers b := by
  induction a with
  | nil => simp [transfers]
  | cons c cs ih => simp only [List.cons_append,transfers,ih,Nat.add_assoc]

def comparator (base : ℕ) : List (Command W) :=
  [.readLeft base,.readRight (base+1),
   .localOp (fun r=>(min r.1 r.2,max r.1 r.2)),
   .writeLeft base,.writeRight (fun _=>base+1)]

theorem comparator_disk (base : ℕ) (s : State W) :
    (execute (comparator base) s).disk=
      Function.update (Function.update s.disk base (min (s.disk base) (s.disk (base+1))))
        (base+1) (max (s.disk base) (s.disk (base+1))) := rfl

theorem comparator_correct (base : ℕ) (s : State W) (x y : W) (xs : List W)
    (hin : FileAt s base (x::y::xs)) :
    FileAt (execute (comparator base) s) base (min x y::max x y::xs) := by
  rw [file_cons,file_cons] at hin ⊢
  rcases hin with ⟨hx,hy,hxs⟩
  refine ⟨?_,?_,?_⟩
  · rw [comparator_disk]
    simp [hx,hy]
  · rw [comparator_disk]
    simp [hx,hy]
  · intro j
    rw [comparator_disk]
    have h0 : base+1+1+j.val≠base := by omega
    have h1 : base+1+1+j.val≠base+1 := by omega
    simpa only [Function.update_of_ne h0,Function.update_of_ne h1] using hxs j

theorem comparator_before (base a : ℕ) (ha : a<base) (s : State W) :
    (execute (comparator base) s).disk a=s.disk a := by
  rw [comparator_disk]
  simp only [Function.update_of_ne (by omega : a≠base),
    Function.update_of_ne (by omega : a≠base+1)]

def insertCode (base : ℕ) : ℕ → List (Command W)
  | 0 => []
  | n+1 => comparator base ++ insertCode (base+1) n

def bubble (x : W) : List W → List W
  | [] => [x]
  | y::ys => min x y::bubble (max x y) ys

theorem insert_before (n base a : ℕ) (ha : a<base) (s : State W) :
    (execute (insertCode base n) s).disk a=s.disk a := by
  induction n generalizing base s with
  | zero => rfl
  | succ n ih =>
    rw [insertCode,execute_append,ih (base+1) (by omega),comparator_before base a ha]

theorem insert_correct (xs : List W) (base : ℕ) (s : State W) (x : W)
    (hin : FileAt s base (x::xs)) :
    FileAt (execute (insertCode base xs.length) s) base (bubble x xs) := by
  induction xs generalizing base s x with
  | nil => exact hin
  | cons y ys ih =>
    have hc := comparator_correct base s x y ys hin
    rw [file_cons] at hc
    have hr := ih (base+1) (execute (comparator base) s) (max x y) hc.2
    rw [List.length_cons,insertCode,execute_append,bubble,file_cons]
    refine ⟨?_,hr⟩
    rw [insert_before ys.length (base+1) base (by omega)]
    exact hc.1

theorem bubble_of_sorted (x : W) (xs : List W) (h : (x::xs).Pairwise (·≤·)) :
    bubble x xs=x::xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    have hh := List.pairwise_cons.mp h
    have hxy := hh.1 y (by simp)
    rw [bubble,min_eq_left hxy,max_eq_right hxy]
    rw [ih y hh.2]

theorem bubble_eq_insert (x : W) (xs : List W) (h : xs.Pairwise (·≤·)) :
    bubble x xs=List.orderedInsert (·≤·) x xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    by_cases hxy : x≤y
    · rw [bubble,min_eq_left hxy,max_eq_right hxy,bubble_of_sorted y ys h]
      simp only [List.orderedInsert,hxy,if_pos]
    · rw [bubble,min_eq_right (le_of_not_ge hxy),max_eq_left (le_of_not_ge hxy),
        ih x (List.pairwise_cons.mp h).2]
      simp only [List.orderedInsert,hxy,if_false]

def sortCode (base : ℕ) : ℕ → List (Command W)
  | 0 => []
  | n+1 => sortCode (base+1) n ++ insertCode base n

theorem sort_before (n base a : ℕ) (ha : a<base) (s : State W) :
    (execute (sortCode base n) s).disk a=s.disk a := by
  induction n generalizing base s with
  | zero => rfl
  | succ n ih =>
    rw [sortCode,execute_append,insert_before n base a ha,ih (base+1) (by omega)]

theorem insert_after (n base a : ℕ) (ha : base+n<a) (s : State W) :
    (execute (insertCode base n) s).disk a=s.disk a := by
  induction n generalizing base s with
  | zero => rfl
  | succ n ih =>
    rw [insertCode,execute_append,ih (base+1) (by omega),comparator_disk]
    simp only [Function.update_of_ne (by omega : a≠base),
      Function.update_of_ne (by omega : a≠base+1)]

theorem sort_after (n base a : ℕ) (ha : base+n≤a) (s : State W) :
    (execute (sortCode base n) s).disk a=s.disk a := by
  induction n generalizing base s with
  | zero => rfl
  | succ n ih =>
    rw [sortCode,execute_append,insert_after n base a (by omega),ih (base+1) (by omega)]

/-- The bounded-input sorter allocates no auxiliary disk region. -/
theorem sort_frame (n base a : ℕ) (ha : a<base ∨ base+n≤a) (s : State W) :
    (execute (sortCode base n) s).disk a=s.disk a := by
  rcases ha with h|h
  · exact sort_before n base a h s
  · exact sort_after n base a h s

theorem sort_correct (xs : List W) (base : ℕ) (s : State W)
    (hin : FileAt s base xs) :
    FileAt (execute (sortCode base xs.length) s) base (xs.insertionSort (·≤·)) := by
  induction xs generalizing base s with
  | nil => exact hin
  | cons x xs ih =>
    rw [file_cons] at hin
    have ht := ih (base+1) s hin.2
    have hh : (execute (sortCode (base+1) xs.length) s).disk base=x := by
      rw [sort_before xs.length (base+1) base (by omega)]
      exact hin.1
    have hi := insert_correct (xs.insertionSort (·≤·)) base
      (execute (sortCode (base+1) xs.length) s) x ((file_cons _ _ _ _).mpr ⟨hh,ht⟩)
    rw [List.length_insertionSort] at hi
    rw [bubble_eq_insert x _ (List.sorted_insertionSort (·≤·) xs)] at hi
    first
    | exact hi
    | (have h_sx := hi; simp only [List.length_cons,sortCode,execute_append,List.insertionSort] at h_sx ⊢; exact h_sx)
    | (have h_sx := hi; simp only [List.length_cons,sortCode,execute_append,List.insertionSort] at h_sx; exact h_sx)
    | (simp only [List.length_cons,sortCode,execute_append,List.insertionSort]; exact hi)

theorem insert_cost (n base : ℕ) : transfers (insertCode (W:=W) base n)=4*n := by
  induction n generalizing base with
  | zero => simp [insertCode,transfers]
  | succ n ih =>
    rw [insertCode,transfers_append,ih]
    simp only [comparator,transfers,cost]
    omega

theorem sort_cost_le (n base : ℕ) : transfers (sortCode (W:=W) base n)≤4*n^2 := by
  induction n generalizing base with
  | zero => simp [sortCode,transfers]
  | succ n ih =>
    rw [sortCode,transfers_append,insert_cost]
    have h := ih (base+1)
    nlinarith

theorem small_cost_le (n base : ℕ) (hn : n≤8) :
    transfers (sortCode (W:=W) base n)≤32*n := by
  have h := sort_cost_le (W:=W) n base
  have hn0 : 0≤n := Nat.zero_le n
  nlinarith

/-- A fixed comparator network selected only by public input length.
No payloads or sorted output are included in the program. -/
def code (w n : ℕ) : List (Stage (Word w)) := [.straight (sortCode 5 n)]

theorem physical_sort {w : ℕ} (n : ℕ) (hn : n≤8) (s : State (Word w))
    (xs : List (Word w)) (hlen : xs.length=n) (hin : File s xs) :
    ∃ t cost, Executes (code w n) s t cost ∧ cost≤32*n ∧
      File t (xs.insertionSort (·≤·)) ∧
      (xs.insertionSort (·≤·)).Perm xs ∧
      (xs.insertionSort (·≤·)).Pairwise (fun x y=>x.val≤y.val) := by
  subst n
  let t := execute (sortCode 5 xs.length) s
  refine ⟨t,transfers (sortCode (W:=Word w) 5 xs.length),?_,
    small_cost_le xs.length 5 hn,sort_correct xs 5 s hin,
    List.perm_insertionSort (·≤·) xs,?_⟩
  · simpa only [code,Nat.add_zero] using
      Executes.straight (sortCode 5 xs.length) [] s t 0 (Executes.done t)
  · exact List.sorted_insertionSort (·≤·) xs

/-- The small-capacity branch of the radix implementation contains at
most eight records; it needs no encoded loop-control tags. -/
theorem small_capacity (w n : ℕ) (hn : n≤2^w) (hcap : ¬12≤2^w) : n≤8 := by
  have hw : w≤3 := by
    by_contra h
    have hp := Nat.pow_le_pow_right (by decide : 1≤2) (show 4≤w by omega)
    norm_num at hp
    omega
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) hw
  norm_num at hp
  omega

end CSL.TwoWordSmallSort
end SmallSort

section BlockFootprint
/-! Syntactic allocation for the two-buffer block execution. Bounds apply
to all resident values and to reads as well as writes, independently of
whether a particular input terminates. -/
set_option autoImplicit false
namespace CSL.TwoWordBlockFootprint
open TwoWordBlockLift
variable {B : ℕ} {W : Type*} [DecidableEq W]

def BoundedCommand (L : ℕ) : Command B W → Prop
  | .readLeft a => a<L
  | .readRight a => ∀ r,a r<L
  | .writeLeft a => a<L
  | .writeRight a => ∀ r,a r<L
  | .cpu _ => True
def BoundedCode (L : ℕ) (code : List (Command B W)) :=
  ∀ cmd∈code,BoundedCommand L cmd

theorem compile_bound (hB : 0<B) (base L : ℕ)
    (cmd : TwoWordPhysicalAddresses.Command W)
    (h : TwoWordRadixFootprint.BoundedCommand L cmd) :
    BoundedCommand (base+L) (compile hB base cmd) := by
  cases cmd <;> simp only [compile,BoundedCommand,
    TwoWordRadixFootprint.BoundedCommand] at *
  all_goals first | omega | exact fun r=>Nat.add_lt_add_left (h _) base | trivial

theorem compiled_code (hB : 0<B) (base L : ℕ)
    (code : List (TwoWordPhysicalAddresses.Command W))
    (h : ∀ cmd∈code,TwoWordRadixFootprint.BoundedCommand L cmd) :
    BoundedCode (base+L) (code.map (compile hB base)) := by
  intro cmd hc
  obtain ⟨c,hmem,heq⟩ := List.mem_map.mp hc
  subst cmd
  exact compile_bound hB base L c (h c hmem)

theorem step_frame (L : ℕ) (cmd : Command B W) (hc : BoundedCommand L cmd)
    (s : State B W) (a : ℕ) (ha : L≤a) : (step cmd s).disk a=s.disk a := by
  cases cmd with
  | readLeft x => rfl
  | readRight x => rfl
  | cpu f => rfl
  | writeLeft x =>
    exact Function.update_of_ne (by change x<L at hc;omega) _ _
  | writeRight f =>
    apply Function.update_of_ne
    have hf := hc (s.left,s.right)
    omega

theorem execute_frame (L : ℕ) (code : List (Command B W)) (hc : BoundedCode L code)
    (s : State B W) (a : ℕ) (ha : L≤a) :
    (execute code s).disk a=s.disk a := by
  induction code generalizing s with
  | nil => rfl
  | cons cmd rest ih =>
    rw [execute,ih (fun c h=>hc c (List.mem_cons_of_mem _ h)),step_frame L cmd
      (hc cmd (List.mem_cons_self)) s a ha]

theorem loop_frame (hB : 0<B) (base L : ℕ) (p : TwoWordUniformLoop.Physical.Program W)
    (hc : TwoWordRadixFootprint.BoundedStage L (.loop p))
    {s t : State B W} {cost : ℕ} (h : LoopExecutes hB base p s t cost)
    (a : ℕ) (ha : base+L≤a) : t.disk a=s.disk a := by
  induction h with
  | stop s h => rfl
  | more s t c h rest ih =>
    rw [ih]
    exact execute_frame (base+L) _ (compiled_code hB base L p.body hc.2)
      (check base p s) a ha

theorem stages_frame (hB : 0<B) (base L : ℕ)
    (code : List (TwoWordRadixPreparedBuild.Stage W))
    (hc : TwoWordRadixFootprint.BoundedCode L code)
    {s t : State B W} {cost : ℕ} (h : Executes hB base code s t cost)
    (a : ℕ) (ha : base+L≤a) : t.disk a=s.disk a := by
  induction h with
  | done s => rfl
  | straight code rest s t c tail ih =>
    rw [ih (fun st h=>hc st (List.mem_cons_of_mem _ h))]
    exact execute_frame (base+L) _
      (compiled_code hB base L code (hc _ List.mem_cons_self)) s a ha
  | loop p rest s mid t ca cb first tail ih =>
    rw [ih (fun st h=>hc st (List.mem_cons_of_mem _ h))]
    exact loop_frame hB base L p (hc _ List.mem_cons_self) first a ha

end CSL.TwoWordBlockFootprint
end BlockFootprint

section BlockFormat
/-! Real compact-file conversion around the two-buffer fallback. An
input word is expanded to the first cell of one sparse block. After
sorting, read-modify-write restores the compact file. Both scans use
only the two existing physical block buffers. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CSL.TwoWordBlockFormat
open TwoWordBlockLift
variable {B : ℕ} {W : Type*} [DecidableEq W]

def cell (hB : 0<B) (i : ℕ) : Fin B := ⟨i%B,Nat.mod_lt _ hB⟩
def wordAt (hB : 0<B) (disk : ℕ→Buffer B W) (i : ℕ) : W := disk (i/B) (cell hB i)
def File (hB : 0<B) (disk : ℕ→Buffer B W) (xs : List W) : Prop :=
  ∀ j : Fin xs.length,wordAt hB disk j.val=xs.get j

theorem execute_append (a b : List (Command B W)) (s : State B W) :
    execute (a++b) s=execute b (execute a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons a rest ih => exact ih (step a s)
theorem transfers_append (a b : List (Command B W)) :
    transfers (a++b)=transfers a+transfers b := by
  induction a with
  | nil => simp only [List.nil_append,transfers,Nat.zero_add]
  | cons a rest ih => simp only [List.cons_append,transfers,ih,Nat.add_assoc]

def expandOne (hB : 0<B) (base k : ℕ) : List (Command B W) :=
  [.readLeft (k/B),.cpu (fun p => (p.1,fun _ => p.1 (cell hB k))),
    .writeRight (fun _ => base+5+k)]
def compressOne (hB : 0<B) (base k : ℕ) : List (Command B W) :=
  [.readLeft (base+5+k),.readRight (fun _ => k/B),
    .cpu (fun p => (p.1,Function.update p.2 (cell hB k) (p.1 ⟨0,hB⟩))),
    .writeRight (fun _ => k/B)]

def expand (hB : 0<B) (base : ℕ) : ℕ→List (Command B W)
  | 0 => []
  | n+1 => expand hB base n++expandOne hB base n
def compress (hB : 0<B) (base : ℕ) : ℕ→List (Command B W)
  | 0 => []
  | n+1 => compress hB base n++compressOne hB base n

theorem expandOne_disk (hB : 0<B) (base k : ℕ) (s : State B W) :
    (execute (expandOne hB base k) s).disk=
      Function.update s.disk (base+5+k) (fun _ => wordAt hB s.disk k) := rfl
theorem compressOne_disk (hB : 0<B) (base k : ℕ) (s : State B W) :
    (execute (compressOne hB base k) s).disk=
      Function.update s.disk (k/B)
        (Function.update (s.disk (k/B)) (cell hB k) (s.disk (base+5+k) ⟨0,hB⟩)) := rfl

theorem expand_cost (hB : 0<B) (base n : ℕ) :
    transfers (expand (W:=W) hB base n)=2*n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [expand,transfers_append,ih]; simp only [expandOne,transfers,cost];omega
theorem compress_cost (hB : 0<B) (base n : ℕ) :
    transfers (compress (W:=W) hB base n)=3*n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [compress,transfers_append,ih]; simp only [compressOne,transfers,cost];omega

theorem expand_frame (hB : 0<B) (base n : ℕ) (s : State B W)
    (a : ℕ) (ha : a<base+5 ∨ base+5+n≤a) :
    (execute (expand hB base n) s).disk a=s.disk a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [expand,execute_append,expandOne_disk,Function.update_of_ne (by omega : a≠base+5+n)]
    exact ih (by omega)

theorem expand_value (hB : 0<B) (base n : ℕ) (s : State B W)
    (hsep : n≤base) (j : ℕ) (hj : j<n) :
    (execute (expand hB base n) s).disk (base+5+j) ⟨0,hB⟩=wordAt hB s.disk j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [expand,execute_append,expandOne_disk]
    by_cases he : j=n
    · subst j
      rw [Function.update_self]
      unfold wordAt
      rw [expand_frame hB base n s (n/B) (Or.inl (by have:=Nat.div_le_self n B;omega))]
    · rw [Function.update_of_ne (by omega : base+5+j≠base+5+n)]
      exact ih (by omega) (by omega)

theorem expand_correct (hB : 0<B) (base n : ℕ) (s : State B W)
    (xs : List W) (hlen : xs.length=n) (hsep : n≤base) (hin : File hB s.disk xs) :
    ∀ j : Fin xs.length,
      (observe hB base (execute (expand hB base n) s)).disk (5+j.val)=xs.get j := by
  intro j
  change (execute (expand hB base n) s).disk (base+(5+j.val)) ⟨0,hB⟩=_
  rw [←Nat.add_assoc,expand_value hB base n s hsep j.val (by have:=j.isLt;omega)]
  exact hin j

theorem compress_frame (hB : 0<B) (base n : ℕ) (s : State B W)
    (hsep : n≤base) (a : ℕ) (ha : base≤a) :
    (execute (compress hB base n) s).disk a=s.disk a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [compress,execute_append,compressOne_disk,
      Function.update_of_ne (by have:=Nat.div_le_self n B;omega : a≠n/B)]
    exact ih (by omega)

theorem compressOne_at (hB : 0<B) (base k : ℕ) (s : State B W) :
    wordAt hB (execute (compressOne hB base k) s).disk k=s.disk (base+5+k) ⟨0,hB⟩ := by
  rw [compressOne_disk]
  simp only [wordAt,Function.update_self]

theorem compressOne_other (hB : 0<B) (base k j : ℕ) (s : State B W) (hne : j≠k) :
    wordAt hB (execute (compressOne hB base k) s).disk j=wordAt hB s.disk j := by
  rw [compressOne_disk]
  unfold wordAt
  by_cases hd : j/B=k/B
  · have hc : cell hB j≠cell hB k := by
      intro he
      have hm : j%B=k%B := congrArg Fin.val he
      have hj := Nat.div_add_mod j B
      have hk := Nat.div_add_mod k B
      rw [hd,hm] at hj
      exact hne (hj.symm.trans hk)
    rw [hd,Function.update_self,Function.update_of_ne hc]
  · rw [Function.update_of_ne hd]

theorem compress_value (hB : 0<B) (base n : ℕ) (s : State B W)
    (hsep : n≤base) (j : ℕ) (hj : j<n) :
    wordAt hB (execute (compress hB base n) s).disk j=s.disk (base+5+j) ⟨0,hB⟩ := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [compress,execute_append]
    by_cases he : j=n
    · subst j
      rw [compressOne_at,compress_frame hB base n s (by omega) (base+5+n) (by omega)]
    · rw [compressOne_other hB base n j _ he]
      exact ih (by omega) (by omega)

theorem compress_correct (hB : 0<B) (base n : ℕ) (s : State B W)
    (xs : List W) (hlen : xs.length=n) (hsep : n≤base)
    (hin : ∀ j : Fin xs.length,(observe hB base s).disk (5+j.val)=xs.get j) :
    File hB (execute (compress hB base n) s).disk xs := by
  intro j
  rw [compress_value hB base n s hsep j.val (by have:=j.isLt;omega)]
  simpa only [observe,Nat.add_assoc] using hin j

end CSL.TwoWordBlockFormat
end BlockFormat

section SmallSortFootprint
/-! Syntactic address bounds for the two-word bounded-input sorter.
All reads and writes remain in its input interval, on every resident state. -/
set_option autoImplicit false
namespace CSL.TwoWordSmallSortFootprint
open TwoWordPhysicalAddresses TwoWordRadixPreparedBuild TwoWordRadixFootprint
open TwoWordSmallSort
variable {W : Type*} [LinearOrder W]

theorem comparator_bound (base L : ℕ) (h : base+1<L) :
    ∀c∈comparator (W:=W) base,BoundedCommand L c := by
  intro c hc
  simp only [comparator,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl
  · change base<L; omega
  · exact h
  · trivial
  · change base<L; omega
  · exact fun _=>h

theorem insert_bound (n base L : ℕ) (h : base+n<L) :
    ∀c∈insertCode (W:=W) base n,BoundedCommand L c := by
  induction n generalizing base with
  | zero => intro c hc; simp [insertCode] at hc
  | succ n ih =>
    intro c hc
    rw [insertCode,List.mem_append] at hc
    rcases hc with hc|hc
    · exact comparator_bound base L (by omega) c hc
    · exact ih (base+1) (by omega) c hc

theorem sort_bound (n base L : ℕ) (h : base+n≤L) :
    ∀c∈sortCode (W:=W) base n,BoundedCommand L c := by
  induction n generalizing base with
  | zero => intro c hc; simp [sortCode] at hc
  | succ n ih =>
    intro c hc
    rw [sortCode,List.mem_append] at hc
    rcases hc with hc|hc
    · exact ih (base+1) (by omega) c hc
    · exact insert_bound n base L (by omega) c hc

theorem code_bound (w n : ℕ) : BoundedCode (5+n) (TwoWordSmallSort.code w n) := by
  intro st hs
  simp only [TwoWordSmallSort.code,List.mem_singleton] at hs
  subst st
  exact sort_bound n 5 (5+n) le_rfl

theorem public_code_bound (w n : ℕ) (hn : n≤2^w) :
    BoundedCode (10+6*2^w) (TwoWordSmallSort.code w n) := by
  intro st hs
  simp only [TwoWordSmallSort.code,List.mem_singleton] at hs
  subst st
  exact sort_bound n 5 _ (by omega)

end CSL.TwoWordSmallSortFootprint
end SmallSortFootprint

section SmallMemoryCore
/-! The public small-memory core selects a constant-round fixed-table
radix sorter, or an at-most-eight-record comparator network when its
control labels do not fit. The choice does not inspect input values. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CSL.TwoWordSmallMemoryCore
open TwoWordRadixInsert (Word)
open TwoWordRadixPreparedBuild (Stage Executes)
open TwoWordPhysicalAddresses (State)
open TwoWordRadixSort (File)

noncomputable def code (w n c : ℕ) (hn : 2≤n) (hword : n≤2^w) : List (Stage (Word w)) :=
  if hcap : 12≤2^w then
    TwoWordUniformRadixSort.code hcap n n (by omega) (by omega) hword hword (2*c)
  else TwoWordSmallSort.code w n

noncomputable def output (w n c : ℕ) (hn : 2≤n) (xs : List (Word w)) : List (Word w) :=
  if 12≤2^w then TwoWordRadixSort.output n (by omega) (2*c) xs
  else xs.insertionSort (·≤·)

def budget (c n : ℕ) : ℕ := (2*c)*(1981*n+96)

theorem budget_linear (c n : ℕ) (hn : 1≤n) : budget c n≤4200*c*n := by
  have hp := Nat.mul_le_mul_left (2*c) (show 1981*n+96≤2100*n by omega)
  unfold budget
  nlinarith only [hp]

theorem small_le_budget (c n : ℕ) (hc : 1≤c) : 32*n≤budget c n := by
  have hp:=Nat.mul_le_mul_right n hc
  unfold budget
  nlinarith only [hp]

theorem output_length (w n c : ℕ) (hn : 2≤n) (xs : List (Word w)) :
    (output w n c hn xs).length=xs.length := by
  unfold output
  split
  · exact TwoWordRadixSort.output_length _ _ _ _
  · exact List.length_insertionSort _ _

theorem word_complete (w n c : ℕ) (hn : 2≤n) (hc : 1≤c)
    (hlower : Nat.clog 2 n≤w) (hupper : w≤c*Nat.clog 2 n)
    (s : State (Word w)) (xs : List (Word w)) (hlen : xs.length=n) (hin : File s xs) :
    ∃ t cost, Executes (code w n c hn ((Nat.le_pow_iff_clog_le (by decide)).2 hlower)) s t cost ∧
      cost≤budget c n ∧ File t (output w n c hn xs) ∧
      (output w n c hn xs).Perm xs ∧
      (output w n c hn xs).Pairwise (fun x y=>x.val≤y.val) := by
  subst n
  by_cases hcap : 12≤2^w
  · obtain ⟨t,ht,hfile,hperm,hsorted⟩ := TwoWordUniformRadixSort.logarithmic_word_sort
      hcap c xs hn hlower hupper s hin
    refine ⟨t,budget c xs.length,?_,le_rfl,?_,?_,?_⟩
    · simpa only [code,dif_pos hcap,budget] using ht
    · simpa only [output,if_pos hcap] using hfile
    · simpa only [output,if_pos hcap] using hperm
    · simpa only [output,if_pos hcap] using hsorted
  · have hN := (Nat.le_pow_iff_clog_le (by decide : 1<2)).2 hlower
    have hsmall := TwoWordSmallSort.small_capacity w xs.length hN hcap
    obtain ⟨t,cost,ht,hcost,hfile,hperm,hsorted⟩ :=
      TwoWordSmallSort.physical_sort xs.length hsmall s xs rfl hin
    refine ⟨t,cost,?_,hcost.trans (small_le_budget c xs.length hc),?_,?_,?_⟩
    · simpa only [code,dif_neg hcap] using ht
    · first
      | exact hfile
      | (have h_sx := hfile; simp only [output,if_neg hcap] at h_sx ⊢; exact h_sx)
      | (have h_sx := hfile; simp only [output,if_neg hcap] at h_sx; exact h_sx)
      | (simp only [output,if_neg hcap]; exact hfile)
    · simpa only [output,if_neg hcap] using hperm
    · simpa only [output,if_neg hcap] using hsorted

theorem code_bound (w n c : ℕ) (hn : 2≤n) (hword : n≤2^w) :
    TwoWordRadixFootprint.BoundedCode (10+6*2^w) (code w n c hn hword) := by
  unfold code
  split
  · exact TwoWordUniformRadixSort.code_bound _ _ _ _ _ _ _ _
  · exact TwoWordSmallSortFootprint.public_code_bound w n hword

/-- The core uses real B-word reads and writes on exactly two resident
block buffers. Its sparse input and output are the observation of this
same physical execution, not a second separately chosen sorting run. -/
theorem block_complete (B w n c base : ℕ) (hB : 0<B) (hn : 2≤n) (hc : 1≤c)
    (hlower : Nat.clog 2 n≤w) (hupper : w≤c*Nat.clog 2 n)
    (s : TwoWordBlockLift.State B (Word w)) (xs : List (Word w)) (hlen : xs.length=n)
    (hin : File (TwoWordBlockLift.observe hB base s) xs) :
    ∃ t cost, TwoWordBlockLift.Executes hB base
        (code w n c hn ((Nat.le_pow_iff_clog_le (by decide)).2 hlower)) s t cost ∧
      cost≤budget c n ∧ File (TwoWordBlockLift.observe hB base t) (output w n c hn xs) ∧
      (output w n c hn xs).Perm xs ∧
      (output w n c hn xs).Pairwise (fun x y=>x.val≤y.val) := by
  obtain ⟨t,cost,ht,hcost,hfile,hperm,hsorted⟩ :=
    word_complete w n c hn hc hlower hupper (TwoWordBlockLift.observe hB base s) xs hlen hin
  obtain ⟨u,hu,he⟩ := TwoWordBlockLift.lift_stages hB base ht s rfl
  exact ⟨u,cost,hu,hcost,by simpa only [he] using hfile,hperm,hsorted⟩

end CSL.TwoWordSmallMemoryCore
end SmallMemoryCore


