-- Prove2me | Definitions.Def_CSL_Sorting_SmallMemory_Radix_Sort
-- name    : CSL_Sorting_SmallMemory_Radix_Sort
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:10:08.456803+00:00
-- url     : https://prove2.me/theorems/d3ea2d9b-de5f-47ab-b723-c502cc54c4bd
-- title:
--   Coded sorting library: Sorting / SmallMemory / Radix / Sort
-- statement:
--   Module `CodedSorting.Sorting.SmallMemory.Radix.Sort` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   One complete physical direct-radix pass, from input words and arbitrary
--   scratch contents to the stable bucket-concatenated output array. The build
--   and gather execute consecutively on the same natural-addressed disk.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.SmallMemory.Radix.Sort

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_SmallMemory_Radix_Initialize

section GatherLoop
set_option autoImplicit false
namespace CSL.TwoWordRadixGather
open TwoWordSpill TwoWordIndirect TwoWordUniformLoop TwoWordRadixInsert

theorem word_val {w : ℕ} (x : Word w) : word x.val=x := by
  apply Fin.ext; exact Nat.mod_eq_of_lt x.isLt

theorem word_add {w : ℕ} (x a b : ℕ) :
    word (w:=w) ((word (w:=w) (x+a)).val+b)=word (x+(a+b)) := by
  apply Fin.ext
  simp only [word,Nat.mod_add_mod,Nat.add_assoc]

theorem writeList_append {w : ℕ} (xs ys : List (Word w)) (out : Word w → Word w)
    (cursor : Word w) :
    writeList (xs++ys) out cursor =
      writeList ys (writeList xs out cursor) (word (cursor.val+xs.length)) := by
  induction xs generalizing out cursor with
  | nil => simp [writeList,word_val]
  | cons x xs ih =>
      rw [List.cons_append,writeList,ih,writeList]
      have he : word ((increment cursor).val+xs.length)=word (w:=w) (cursor.val+(x::xs).length) := by
        apply Fin.ext
        simp only [increment,word,List.length_cons,Nat.mod_add_mod]
        congr 1
        omega
      rw [he]

theorem bucket_runs {w n K : ℕ} (hcap : 11 ≤ 2^w) (hN : n≤2^w) (hK : K≤2^w)
    (last : Word w) (input : Fin n → Word w) (heap : DirectRadix.Heap n K)
    (ids : List (Fin n)) (k : Fin K) (v : State w)
    (hc : DirectRadix.Chain heap.next (heap.head k) ids) (hr : HeapRep hcap hN hK heap v)
    (hin : ∀ i, v.regs (.inr (0,position hN i))=input i)
    (hp : v.pc=label hcap 0) (hk : v.regs (.inl 0)=position hK k) :
    ∃ t, Runs hcap last (6*ids.length+4) v t ∧
      t.pc=(if position hK k=last then label hcap 9 else label hcap 0) ∧
      Preserves v t ∧ t.regs (.inl 0)=increment (position hK k) ∧
      t.regs (.inl 4)=word ((v.regs (.inl 4)).val+ids.length) ∧
      (fun x => t.regs (.inr (5,x)))=
        writeList (ids.map input) (fun x => v.regs (.inr (5,x))) (v.regs (.inl 4)) := by
  let headed := header hcap last v
  have hd : ∀ (r : Fin 6) (x : Word w), headed.regs (.inr (r,x))=v.regs (.inr (r,x)) := by
    intro r x; simp [headed,header,instruction,effect,loadEffect]
  have hpres : Preserves v headed := fun r x _ => hd r x
  have hip : ∀ i, headed.regs (.inr (0,position hN i))=input i := by
    intro i; rw [hd]; exact hin i
  have hv : headed.regs (.inl 1)=pointerValue hcap hN (heap.head k) := by
    simp [headed,header,instruction,effect,loadEffect,hk,hr.headValue]
  have hb : headed.regs (.inl 2)=pointerValid hcap (heap.head k) := by
    simp [headed,header,instruction,effect,loadEffect,hk,hr.headValid]
  obtain ⟨walked,hw,hwp,hpres',hbucket,hcursor,hout⟩ := walk_runs hcap hN hK last input heap
    ids (heap.head k) headed hc (hr.of_preserves hpres) hip rfl hv hb
  have hbk : walked.regs (.inl 0)=position hK k := by
    rw [hbucket]; simpa [headed,header,instruction,effect,loadEffect] using hk
  refine ⟨advance hcap last walked,?_,?_,?_,?_,?_,?_⟩
  · convert (header_runs hcap last v hp).trans (hw.trans (advance_runs hcap last walked hwp))
      using 1 <;> omega
  · simp [advance,instruction,arithmetic,effect,applyInstruction,hbk]
  · apply (hpres.trans hpres').trans
    intro r x _; simp [advance,instruction,arithmetic,effect,applyInstruction]
  · simp [advance,instruction,arithmetic,effect,applyInstruction,hbk]
  · simpa [advance,instruction,arithmetic,effect,applyInstruction,
      headed,header,loadEffect] using hcursor
  · simpa [advance,instruction,arithmetic,effect,applyInstruction,
      headed,header,loadEffect] using hout

def order {n K : ℕ} (lists : Fin K → List (Fin n)) :
    (start count : ℕ) → start+count≤K → List (Fin n)
  | _,0,_ => []
  | start,count+1,h => lists ⟨start,by omega⟩ ++ order lists (start+1) count (by omega)

theorem order_ofFn {n K : ℕ} (lists : Fin K → List (Fin n)) (start count : ℕ)
    (h : start+count≤K) :
    order lists start count h =
      (List.ofFn (fun j : Fin count => lists ⟨start+j.val,by omega⟩)).flatten := by
  induction count generalizing start with
  | zero => simp [order]
  | succ count ih =>
      rw [order,ih,List.ofFn_succ,List.flatten_cons]
      congr 2
      congr 1
      funext i
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

theorem order_all {n K : ℕ} (lists : Fin K → List (Fin n)) :
    order lists 0 K (by omega) = ((List.finRange K).map lists).flatten := by
  rw [order_ofFn]
  simp [List.finRange, List.map_ofFn]
  rfl

theorem suffix_runs {w n K : ℕ} (hcap : 11 ≤ 2^w) (hN : n≤2^w) (hK : K≤2^w)
    (hk : 0<K) (input : Fin n → Word w) (heap : DirectRadix.Heap n K)
    (lists : Fin K → List (Fin n)) (hchain : DirectRadix.Represents heap lists)
    (count start : ℕ) (hcount : start+(count+1)=K) (v : State w)
    (hr : HeapRep hcap hN hK heap v)
    (hin : ∀ i, v.regs (.inr (0,position hN i))=input i)
    (hp : v.pc=label hcap 0) (hbucket : v.regs (.inl 0)=position hK ⟨start,by omega⟩) :
    ∃ t, Runs hcap (position hK ⟨K-1,by omega⟩)
      (6*(order lists start (count+1) (by omega)).length+4*(count+1)) v t ∧
      t.pc=label hcap 9 ∧ Preserves v t ∧
      (fun x => t.regs (.inr (5,x)))=
        writeList ((order lists start (count+1) (by omega)).map input)
          (fun x => v.regs (.inr (5,x))) (v.regs (.inl 4)) := by
  induction count generalizing start v with
  | zero =>
      obtain ⟨t,ht,hpc,hpres,hbk,hcursor,hout⟩ := bucket_runs hcap hN hK
        (position hK ⟨K-1,by omega⟩) input heap (lists ⟨start,by omega⟩)
        ⟨start,by omega⟩ v (hchain _) hr hin hp hbucket
      have he : (⟨start,by omega⟩ : Fin K)=⟨K-1,by omega⟩ := by
        apply Fin.ext; change start=K-1; omega
      refine ⟨t,?_,?_,hpres,?_⟩
      · simpa [order] using ht
      · simpa [he] using hpc
      · simpa [order] using hout
  | succ count ih =>
      obtain ⟨mid,hm,hmp,hpres,hbk,hcursor,hout⟩ := bucket_runs hcap hN hK
        (position hK ⟨K-1,by omega⟩) input heap (lists ⟨start,by omega⟩)
        ⟨start,by omega⟩ v (hchain _) hr hin hp hbucket
      have hne : (⟨start,by omega⟩ : Fin K)≠⟨K-1,by omega⟩ := by
        intro he; have he' : start=K-1 := congrArg Fin.val he; omega
      have hp' : mid.pc=label hcap 0 := by simpa [position_eq,hne] using hmp
      have hb' : mid.regs (.inl 0)=position hK ⟨start+1,by omega⟩ := by
        rw [hbk]
        apply Fin.ext
        change (start+1)%2^w=start+1
        exact Nat.mod_eq_of_lt (by omega)
      have hi' : ∀ i, mid.regs (.inr (0,position hN i))=input i := by
        intro i; rw [hpres 0 _ (by decide)]; exact hin i
      obtain ⟨t,ht,htp,hpres',hout'⟩ := ih (start+1) (by omega) mid
        (hr.of_preserves hpres) hi' hp' hb'
      refine ⟨t,?_,htp,hpres.trans hpres',?_⟩
      · convert hm.trans ht using 1
        simp only [order,List.length_append]
        omega
      · rw [hout',hout,hcursor]
        simp only [order,List.map_append,writeList_append,List.length_map]

/-- The complete fixed nine-instruction program follows the actual head and
next pointers in increasing bucket order. It never writes input or links. -/
theorem physical_gather {w n K : ℕ} (hcap : 11 ≤ 2^w) (hN : n≤2^w) (hK : K≤2^w)
    (hk : 0<K) (input : Fin n → Word w) (heap : DirectRadix.Heap n K)
    (lists : Fin K → List (Fin n)) (hchain : DirectRadix.Represents heap lists)
    (s : TwoWordPhysicalAddresses.State (Word w))
    (hr : HeapRep hcap hN hK heap (view 5 6 w s))
    (hin : ∀ i, (view 5 6 w s).regs (.inr (0,position hN i))=input i)
    (hp : (view 5 6 w s).pc=label hcap 0)
    (hb : (view 5 6 w s).regs (.inl 0)=position hK ⟨0,hk⟩) :
    ∃ t, Physical.Executes
      (program 5 6 w (table hcap (position hK ⟨K-1,by omega⟩)) (label hcap 9)) s t
      (384*((List.finRange K).map lists).flatten.length+256*K+1) ∧
      Preserves (view 5 6 w s) (view 5 6 w t) ∧
      (fun x => (view 5 6 w t).regs (.inr (5,x)))=
        writeList ((((List.finRange K).map lists).flatten).map input)
          (fun x => (view 5 6 w s).regs (.inr (5,x))) ((view 5 6 w s).regs (.inl 4)) := by
  obtain ⟨final,hf,hp',hpres,hout⟩ := suffix_runs hcap hN hK hk input heap lists hchain
    (K-1) 0 (by omega) (view 5 6 w s) hr hin hp hb
  have hK' : K-1+1=K := by omega
  simp only [hK',order_all] at hf hout
  obtain ⟨t,ht,hv⟩ := terminates_of_source 5 6 w _ (label hcap 9) _ s final (hf.halts hp')
  refine ⟨t,?_,?_,?_⟩
  · convert ht using 1 <;> rw [table_cost] <;> omega
  · rw [hv]; exact hpres
  · rw [hv]; exact hout

end CSL.TwoWordRadixGather
end GatherLoop

section Pass
/-! One complete physical direct-radix pass, from input words and arbitrary
scratch contents to the stable bucket-concatenated output array. The build
and gather execute consecutively on the same natural-addressed disk. -/

set_option autoImplicit false
namespace CSL.TwoWordRadixPass
open TwoWordSpill TwoWordUniformLoop TwoWordRadixInsert TwoWordRadixGather
open TwoWordRadixPreparedBuild

theorem writeList_before {w : ℕ} (xs : List (Word w)) (out : Word w → Word w)
    (start : ℕ) (hbound : start+xs.length≤2^w) (x : Word w) (hx : x.val<start) :
    writeList xs out (word start) x=out x := by
  induction xs generalizing out start with
  | nil => rfl
  | cons a xs ih =>
      rw [writeList,increment_word,ih _ (start+1) (by simp only [List.length_cons] at hbound; omega)
        (by omega)]
      apply Function.update_of_ne
      intro he
      have hstart : start<2^w := by simp only [List.length_cons] at hbound; omega
      have hv := congrArg (fun q : Word w => q.val) he
      simp only [word,Nat.mod_eq_of_lt hstart] at hv
      omega

theorem writeList_get {w : ℕ} (xs : List (Word w)) (out : Word w → Word w)
    (start : ℕ) (hbound : start+xs.length≤2^w) (j : ℕ) (hj : j<xs.length) :
    writeList xs out (word start) (word (start+j))=xs[j] := by
  induction xs generalizing out start j with
  | nil => simp at hj
  | cons a xs ih =>
      have hstart : start<2^w := by simp only [List.length_cons] at hbound; omega
      cases j with
      | zero =>
          rw [writeList,increment_word]
          simp only [Nat.add_zero,List.getElem_cons_zero]
          rw [writeList_before xs _ (start+1) (by simp only [List.length_cons] at hbound; omega)
            (word start) (by simpa [word,Nat.mod_eq_of_lt hstart] using Nat.lt_succ_self start)]
          simp
      | succ j =>
          rw [writeList,increment_word]
          have hj' : j<xs.length := by simpa using hj
          have he : start+(j+1)=(start+1)+j := by omega
          simp only [List.getElem_cons_succ,he]
          exact ih _ (start+1) (by simp only [List.length_cons] at hbound; omega) j hj'

/-- Adding the output region leaves every existing data address unchanged.
Only control-cell addresses move, and the new PC is explicitly initialized. -/
theorem view_data_address {w regions : ℕ} (s : TwoWordPhysicalAddresses.State (Word w))
    (r : Fin regions) (x : Word w) :
    (view 5 regions w s).regs (.inr (r,x))=s.disk (5+r.val*2^w+x.val) := by
  change s.disk (TwoWordPhysicalAddresses.addressNumber 5 regions w (.reg (.inr (r,x))))=_
  rw [TwoWordPhysicalAddresses.data_address]

theorem same_data {w : ℕ} (s : TwoWordPhysicalAddresses.State (Word w))
    (r : Fin 5) (x : Word w) :
    (view 5 6 w s).regs (.inr (r.castSucc,x))=(view 5 5 w s).regs (.inr (r,x)) := by
  rw [view_data_address,view_data_address]; rfl

def setupAbstract {w : ℕ} (hcap : 11≤2^w) :
    List (TwoWordSpill.Command (TwoWordPhysicalAddresses.Register 5 6 w) (Word w)) :=
  [.localOp (fun _ => (label hcap 0,label hcap 0)),
   .writeLeft (.reg (.inl 0)),.writeLeft (.reg (.inl 4)),.writeRight (fun _ => .pc)]

def setup {w : ℕ} (hcap : 11≤2^w) : List (TwoWordPhysicalAddresses.Command (Word w)) :=
  (setupAbstract hcap).map (TwoWordPhysicalAddresses.compile (TwoWordPhysicalAddresses.addressNumber 5 6 w))

def setupState {w : ℕ} (hcap : 11≤2^w) (s : TwoWordPhysicalAddresses.State (Word w)) :=
  TwoWordPhysicalAddresses.execute (setup hcap) s

theorem setup_cost {w : ℕ} (hcap : 11≤2^w) :
    TwoWordPhysicalAddresses.transfers (setup hcap)=3 := by
  rw [setup,TwoWordPhysicalAddresses.transfers_compile]; rfl

theorem setup_view {w : ℕ} (hcap : 11≤2^w) (s : TwoWordPhysicalAddresses.State (Word w)) :
    view 5 6 w (setupState hcap s)=
      ⟨Function.update (Function.update (view 5 6 w s).regs (.inl 0) (label hcap 0))
        (.inl 4) (label hcap 0),label hcap 0⟩ := by
  unfold view setupState setup
  rw [TwoWordPhysicalAddresses.execute_pullback _ (TwoWordPhysicalAddresses.addressNumber_injective 5 6 w)]
  simp [setupAbstract,TwoWordSpill.execute,TwoWordSpill.step,observe,resident]
  funext r
  simp [Function.update_apply]

theorem setup_data {w : ℕ} (hcap : 11≤2^w) (s : TwoWordPhysicalAddresses.State (Word w))
    (r : Fin 6) (x : Word w) :
    (view 5 6 w (setupState hcap s)).regs (.inr (r,x))=(view 5 6 w s).regs (.inr (r,x)) := by
  rw [setup_view]; simp

theorem executes_append {w : ℕ} {a b : List (Stage (Word w))}
    {s mid t : TwoWordPhysicalAddresses.State (Word w)} {ca cb : ℕ}
    (ha : Executes a s mid ca) (hb : Executes b mid t cb) :
    Executes (a++b) s t (ca+cb) := by
  induction ha with
  | done s => simpa using hb
  | straight code rest s mid cost tail ih =>
      simpa [Nat.add_assoc] using Executes.straight code (rest++b) s t _ (ih hb)
  | loop p rest s next mid firstCost restCost first tail ih =>
      simpa [Nat.add_assoc] using Executes.loop p (rest++b) s next t _ _ first (ih hb)

def code {w : ℕ} (hcap : 12≤2^w) (headLast inputLast : Word w)
    (key : Word w → Word w) : List (Stage (Word w)) :=
  TwoWordRadixPreparedBuild.code hcap headLast inputLast key ++
    [.straight (setup (TwoWordRadixBuild.smallCap hcap)),
     .loop (program 5 6 w (TwoWordRadixGather.table (TwoWordRadixBuild.smallCap hcap) headLast)
       (label (TwoWordRadixBuild.smallCap hcap) 9))]

/-- Actual build and actual gather form one physical stable radix pass.
All directory initialization, scalar resets, PC reads, indirect data reads,
link accesses and output stores are included in this same execution count.
The input and output each have one word per B=1 disk block. -/
theorem physical_pass {w K : ℕ} (hcap : 12≤2^w) (hK : K≤2^w) (hk : 0<K)
    (xs : List (Word w)) (hn : 0<xs.length) (hN : xs.length≤2^w)
    (key : Word w → Fin K) (s : TwoWordPhysicalAddresses.State (Word w))
    (hin : ∀ j, (view 5 5 w s).regs (.inr (0,position hN j))=xs.get j) :
    ∃ t, Executes
      (code hcap (position hK ⟨K-1,by omega⟩) (position hN ⟨xs.length-1,by omega⟩)
        (fun x => position hK (key x))) s t (1527*xs.length+376*K+93) ∧
      (∀ j, (view 5 6 w t).regs (.inr (0,position hN j))=xs.get j) ∧
      (∀ j (hj : j<(BucketMachine.collect key xs).length),
        (view 5 6 w t).regs (.inr (5,word j))=(BucketMachine.collect key xs)[j]) := by
  let cap := TwoWordRadixBuild.smallCap hcap
  let lists := BucketMachine.bucket (fun j => key (xs.get j)) (List.finRange xs.length)
  let heap := DirectRadix.build (fun j => key (xs.get j)) (List.finRange xs.length)
  obtain ⟨built,hbuild,hrep,hi⟩ := physical_prepared_build hcap hN hK hn hk xs.get key s hin
  let ready := setupState cap built
  have hd : ∀ (r : Fin 6) (r' : Fin 5), r.val=r'.val → ∀ (x : Word w),
      (view 5 6 w ready).regs (.inr (r,x))=(view 5 5 w built).regs (.inr (r',x)) := by
    intro r r' he x; rw [setup_data,view_data_address,view_data_address,he]
  have hr : HeapRep cap hN hK heap (view 5 6 w ready) := by
    constructor
    · intro k; rw [hd 1 1 rfl]; exact hrep.headValue k
    · intro k; rw [hd 2 2 rfl]; exact hrep.headValid k
    · intro i; rw [hd 3 3 rfl]; exact hrep.nextValue i
    · intro i; rw [hd 4 4 rfl]; exact hrep.nextValid i
  have hir : ∀ j, (view 5 6 w ready).regs (.inr (0,position hN j))=xs.get j := by
    intro j; rw [hd 0 0 rfl]; exact hi j
  have hpr : (view 5 6 w ready).pc=label cap 0 := by rw [setup_view]
  have hbr : (view 5 6 w ready).regs (.inl 0)=position hK ⟨0,hk⟩ := by
    rw [setup_view]; simp [label,position]; apply Fin.ext; rfl
  have hcur : (view 5 6 w ready).regs (.inl 4)=word 0 := by
    rw [setup_view]; simp [label,word]; apply Fin.ext; rfl
  have hchain : DirectRadix.Represents heap lists :=
    DirectRadix.build_represents _ _ (List.nodup_finRange _)
  obtain ⟨t,hgather,hpres,hout⟩ := physical_gather cap hN hK hk xs.get heap lists hchain ready hr hir hpr hbr
  have hlen : ((List.finRange K).map lists).flatten.length=xs.length := by
    simpa [BucketMachine.collect,lists,List.flatMap] using
      BucketMachine.collect_length (fun j => key (xs.get j)) (List.finRange xs.length)
  have horder : (((List.finRange K).map lists).flatten).map xs.get=BucketMachine.collect key xs := by
    have h := DirectRadix.collect_map key xs.get (List.finRange xs.length)
    rw [List.finRange_map_get] at h
    exact h.symm
  rw [horder,hcur] at hout
  refine ⟨t,?_,?_,?_⟩
  · have hg := Executes.straight (setup cap) _ built t _
      (Executes.loop _ [] ready t t _ 0 hgather (Executes.done t))
    have hall := executes_append hbuild hg
    convert hall using 1
    all_goals first | rfl | (rw [setup_cost,hlen]; omega) | omega
  · intro j; rw [hpres 0 _ (by decide)]; exact hir j
  · intro j hj
    have he := congrFun hout (word j)
    apply he.trans
    simpa only [Nat.zero_add] using writeList_get (BucketMachine.collect key xs) _ 0
      (by simpa [BucketMachine.collect_length] using hN) j hj

/-- The same endpoint stated directly on natural block addresses. The input
occupies [5,5+N); the output occupies [5+5*2^w,5+5*2^w+N). -/
theorem physical_pass_disk {w K : ℕ} (hcap : 12≤2^w) (hK : K≤2^w) (hk : 0<K)
    (xs : List (Word w)) (hn : 0<xs.length) (hN : xs.length≤2^w)
    (key : Word w → Fin K) (s : TwoWordPhysicalAddresses.State (Word w))
    (hin : ∀ j : Fin xs.length, s.disk (5+j.val)=xs.get j) :
    ∃ t, Executes
      (code hcap (position hK ⟨K-1,by omega⟩) (position hN ⟨xs.length-1,by omega⟩)
        (fun x => position hK (key x))) s t (1527*xs.length+376*K+93) ∧
      (∀ j : Fin xs.length, t.disk (5+j.val)=xs.get j) ∧
      (∀ j (hj : j<(BucketMachine.collect key xs).length),
        t.disk (5+5*2^w+j)=(BucketMachine.collect key xs)[j]) := by
  have hi : ∀ j, (view 5 5 w s).regs (.inr (0,position hN j))=xs.get j := by
    intro j; rw [view_data_address]; simpa [position] using hin j
  obtain ⟨t,ht,hi',ho⟩ := physical_pass hcap hK hk xs hn hN key s hi
  refine ⟨t,ht,?_,?_⟩
  · intro j; have h := hi' j; rw [view_data_address] at h; simpa [position] using h
  · intro j hj
    have hj' : j<2^w := by rw [BucketMachine.collect_length] at hj; omega
    have h := ho j hj
    rw [view_data_address] at h
    simpa [word,Nat.mod_eq_of_lt hj'] using h

end CSL.TwoWordRadixPass
end Pass

section Copy
/-! A public-size copy schedule between the two data banks. Each word is
actually read and written using the existing two resident words. The schedule
is generated from N, never from input values or a data-dependent time bound. -/
set_option autoImplicit false
namespace CSL.TwoWordRadixCopy
open TwoWordRadixInsert TwoWordPhysicalAddresses

def code (w : ℕ) : ℕ → List (Command (Word w))
  | 0 => []
  | n+1 => .readLeft (5+5*2^w+n) :: .writeLeft (5+n) :: code w n

@[simp] theorem cost (w n : ℕ) : transfers (code w n)=2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [code,transfers,TwoWordPhysicalAddresses.cost,ih]; omega

theorem outside (w n : ℕ) (s : State (Word w)) (a : ℕ)
    (ha : a<5 ∨ 5+n≤a) : (execute (code w n) s).disk a=s.disk a := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [code,execute]
    rw [ih _ (by omega)]
    simp only [step]
    have hne : a≠5+n := by omega
    exact Function.update_of_ne hne _ _

/-- The input and output offsets fit in one word; fixed bank numbers belong
only to the public code's effective-address function. -/
theorem correct (w n : ℕ) (hN : n≤2^w) (s : State (Word w)) :
    ∀ j, j<n → (execute (code w n) s).disk (5+j)=s.disk (5+5*2^w+j) := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    intro j hj
    simp only [code,execute]
    by_cases he : j=n
    · subst j
      rw [outside _ _ _ _ (by omega)]
      simp only [step,Function.update_self]
    · have hj' : j<n := by omega
      rw [ih (by omega) _ j hj']
      simp only [step]
      apply Function.update_of_ne
      have hp : 0<2^w := Nat.two_pow_pos w
      omega

end CSL.TwoWordRadixCopy
end Copy

section «Sort»
/-! Complete least-significant-digit sorting on one physical word disk.
All records, directory cells, resets and inter-round copies belong to one
`Executes` derivation. Only public N, radix and round count generate code;
no input list or intermediate histogram is captured by that code. This
endpoint retains the atomic-effective-address model of the base simulator. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CSL.TwoWordRadixSort
open TwoWordRadixInsert TwoWordRadixPreparedBuild
open TwoWordPhysicalAddresses (State)

abbrev File {w : ℕ} (s : State (Word w)) (xs : List (Word w)) : Prop :=
  ∀ j : Fin xs.length, s.disk (5+j.val)=xs.get j

def digit {w : ℕ} (K : ℕ) (hk : 0<K) (round : ℕ) (x : Word w) : Fin K :=
  MSD.digit K hk round x.val

def output {w : ℕ} (K : ℕ) (hk : 0<K) : ℕ → List (Word w) → List (Word w)
  | 0,xs => xs
  | r+1,xs => BucketMachine.collect (digit K hk r) (output K hk r xs)

theorem output_perm {w : ℕ} (K : ℕ) (hk : 0<K) (r : ℕ) (xs : List (Word w)) :
    (output K hk r xs).Perm xs := by
  induction r with
  | zero => exact List.Perm.refl _
  | succ r ih => exact (BucketMachine.collect_perm _ _).trans ih

@[simp] theorem output_length {w : ℕ} (K : ℕ) (hk : 0<K) (r : ℕ) (xs : List (Word w)) :
    (output K hk r xs).length=xs.length := (output_perm K hk r xs).length_eq

theorem output_values {w : ℕ} (K : ℕ) (hk : 0<K) (r : ℕ) (xs : List (Word w)) :
    (output K hk r xs).map Fin.val=DirectRadix.lsd K hk r (xs.map Fin.val) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (BucketMachine.collect (fun x : Word w => MSD.digit K hk r x.val)
      (output K hk r xs)).map Fin.val = _
    rw [←DirectRadix.collect_map (MSD.digit K hk r) Fin.val,ih]
    rfl

theorem output_sorted {w : ℕ} (K : ℕ) (hk : 0<K) (r : ℕ) (xs : List (Word w))
    (hb : ∀ x∈xs,x.val<K^r) :
    (output K hk r xs).Pairwise (fun x y => x.val≤y.val) := by
  have h : ∀ x∈xs.map Fin.val,x<K^r := by
    intro x hx; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx; exact hb a ha
  have hs := (DirectRadix.lsd_correct K hk r (xs.map Fin.val) h).2
  rw [←output_values] at hs
  simpa only [List.pairwise_map] using hs

def roundCode {w : ℕ} (hcap : 12≤2^w) (n K : ℕ) (hn : 0<n) (hk : 0<K)
    (hN : n≤2^w) (hK : K≤2^w) (key : Word w → Fin K) : List (Stage (Word w)) :=
  TwoWordRadixPass.code hcap (position hK ⟨K-1,by omega⟩)
    (position hN ⟨n-1,by omega⟩) (fun x => position hK (key x)) ++
  [.straight (TwoWordRadixCopy.code w n)]

theorem round_correct {w : ℕ} (hcap : 12≤2^w) (n K : ℕ) (hn : 0<n) (hk : 0<K)
    (hN : n≤2^w) (hK : K≤2^w) (key : Word w → Fin K)
    (s : State (Word w)) (xs : List (Word w)) (hlen : xs.length=n) (hin : File s xs) :
    ∃ t, Executes (roundCode hcap n K hn hk hN hK key) s t (1529*n+376*K+93) ∧
      File t (BucketMachine.collect key xs) := by
  subst n
  obtain ⟨t,ht,_,hout⟩ := TwoWordRadixPass.physical_pass_disk hcap hK hk xs hn hN key s hin
  let t' := TwoWordPhysicalAddresses.execute (TwoWordRadixCopy.code w xs.length) t
  have hc : Executes [.straight (TwoWordRadixCopy.code w xs.length)] t t' (2*xs.length) := by
    simpa only [TwoWordRadixCopy.cost,Nat.add_zero] using
      Executes.straight (TwoWordRadixCopy.code w xs.length) [] t t' 0 (Executes.done t')
  refine ⟨t',?_,?_⟩
  · have he := TwoWordRadixPass.executes_append ht hc
    convert he using 1
    all_goals first | rfl | omega
  · intro j
    have hj : j.val<xs.length := by simpa only [BucketMachine.collect_length] using j.isLt
    exact (TwoWordRadixCopy.correct w xs.length hN t j.val hj).trans (hout j.val j.isLt)

def code {w : ℕ} (hcap : 12≤2^w) (n K : ℕ) (hn : 0<n) (hk : 0<K)
    (hN : n≤2^w) (hK : K≤2^w) : ℕ → List (Stage (Word w))
  | 0 => []
  | r+1 => code hcap n K hn hk hN hK r ++
      roundCode hcap n K hn hk hN hK (digit K hk r)

/-- Exact cost and exact final data refer to this one complete physical run. -/
theorem physical_sort {w : ℕ} (hcap : 12≤2^w) (n K : ℕ) (hn : 0<n) (hk : 0<K)
    (hN : n≤2^w) (hK : K≤2^w) (r : ℕ) (s : State (Word w))
    (xs : List (Word w)) (hlen : xs.length=n) (hin : File s xs) :
    ∃ t, Executes (code hcap n K hn hk hN hK r) s t (r*(1529*n+376*K+93)) ∧
      File t (output K hk r xs) := by
  induction r with
  | zero => exact ⟨s,by simpa only [code,Nat.zero_mul] using Executes.done s,hin⟩
  | succ r ih =>
    obtain ⟨mid,hm,hfile⟩ := ih
    obtain ⟨t,ht,hout⟩ := round_correct hcap n K hn hk hN hK (digit K hk r)
      mid (output K hk r xs) (by simpa only [output_length] using hlen) hfile
    refine ⟨t,?_,hout⟩
    change Executes (code hcap n K hn hk hN hK r ++
      roundCode hcap n K hn hk hN hK (digit K hk r)) s t _
    rw [Nat.succ_mul]
    exact TwoWordRadixPass.executes_append hm ht

/-- Standard logarithmic-address branch: the lower word bound is explicit.
The fixed 12-label implementation also requires 12≤2^w; no word is widened. -/
theorem logarithmic_word_sort {w : ℕ} (hcap : 12≤2^w) (c : ℕ)
    (xs : List (Word w)) (hN : 2≤xs.length)
    (hlower : Nat.clog 2 xs.length≤w) (hupper : w≤c*Nat.clog 2 xs.length)
    (s : State (Word w)) (hin : File s xs) :
    ∃ t, Executes (code hcap xs.length xs.length (by omega) (by omega)
        ((Nat.le_pow_iff_clog_le (by decide)).2 hlower)
        ((Nat.le_pow_iff_clog_le (by decide)).2 hlower) (2*c))
      s t ((2*c)*(1905*xs.length+93)) ∧
      File t (output xs.length (by omega) (2*c) xs) ∧
      (output xs.length (by omega) (2*c) xs).Perm xs ∧
      (output xs.length (by omega) (2*c) xs).Pairwise (fun x y => x.val≤y.val) := by
  have hn : 0<xs.length := by omega
  have hword : xs.length≤2^w := (Nat.le_pow_iff_clog_le (by decide)).2 hlower
  obtain ⟨t,ht,hout⟩ := physical_sort hcap xs.length xs.length hn hn hword hword
    (2*c) s xs rfl hin
  refine ⟨t,?_,hout,output_perm _ _ _ _,output_sorted _ _ _ _ ?_⟩
  · convert ht using 1; congr 1; ring
  · intro x hx
    exact DirectRadix.word_universe_bound xs.length c w x.val hN hupper x.isLt

end CSL.TwoWordRadixSort
end «Sort»

section Footprint
/-! Every effective address of the full radix program lies in one fixed
finite disk interval, even on arbitrary resident values. No successful-run
hypothesis is needed for this syntactic allocation bound. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CSL.TwoWordRadixFootprint
open TwoWordRadixInsert TwoWordPhysicalAddresses TwoWordRadixPreparedBuild

variable {W : Type*}

def BoundedCommand (L : ℕ) : Command W → Prop
  | .readLeft a => a<L
  | .readRight a => a<L
  | .readRightAt a => ∀r,a r<L
  | .writeLeft a => a<L
  | .writeRight a => ∀r,a r<L
  | .localOp _ => True

def BoundedStage (L : ℕ) : Stage W → Prop
  | .straight cmds => ∀c∈cmds,BoundedCommand L c
  | .loop p => p.pcAddress<L ∧ ∀c∈p.body,BoundedCommand L c

def BoundedCode (L : ℕ) (code : List (Stage W)) := ∀s∈code,BoundedStage L s

theorem compile_bound {R : Type*} (L : ℕ) (address : TwoWordSpill.Address R → ℕ)
    (ha : ∀a,address a<L) (c : TwoWordSpill.Command R W) :
    BoundedCommand L (compile address c) := by
  cases c <;> simp only [compile,BoundedCommand] <;> first | exact ha _ | exact fun _=>ha _ | trivial

theorem compiled_code (r regions w L : ℕ) (h : r+regions*2^w+5≤L)
    (cmds : List (TwoWordSpill.Command (Register r regions w) (Word w))) :
    BoundedStage L (.straight (cmds.map (compile (addressNumber r regions w)))) := by
  intro c hc
  obtain ⟨cmd,_,rfl⟩ := List.mem_map.mp hc
  exact compile_bound L _ (fun a=>(addressNumber_bound r regions w a).trans_le h) cmd

theorem program_bound (r regions w L : ℕ) (h : r+regions*2^w+5≤L)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Word w)) (halt : Word w) :
    BoundedStage L (.loop (TwoWordUniformLoop.program r regions w table halt)) := by
  constructor
  · exact (addressNumber_bound r regions w .pc).trans_le h
  · exact compiled_code r regions w L h _

theorem copy_bound (w n : ℕ) (hn : n≤2^w) :
    BoundedStage (10+6*2^w) (.straight (TwoWordRadixCopy.code w n)) := by
  induction n with
  | zero => intro c hc; simp [TwoWordRadixCopy.code] at hc
  | succ n ih =>
    intro c hc
    simp only [TwoWordRadixCopy.code,List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · change 5+5*2^w+n<10+6*2^w; omega
    · change 5+n<10+6*2^w; omega
    · exact ih (by omega) c hc

theorem round_bound {w : ℕ} (hcap : 12≤2^w) (n K : ℕ) (hn : 0<n) (hk : 0<K)
    (hN : n≤2^w) (hK : K≤2^w) (key : Word w→Fin K) :
    BoundedCode (10+6*2^w) (TwoWordRadixSort.roundCode hcap n K hn hk hN hK key) := by
  have h5 : 5+5*2^w+5≤10+6*2^w := by omega
  have h6 : 5+6*2^w+5≤10+6*2^w := by omega
  intro st hs
  simp only [TwoWordRadixSort.roundCode,TwoWordRadixPass.code,
    TwoWordRadixPreparedBuild.code,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with ((rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl) | rfl
  · exact compiled_code 5 5 w _ h5 _
  · exact program_bound 5 5 w _ h5 _ _
  · exact compiled_code 5 5 w _ h5 _
  · exact program_bound 5 5 w _ h5 _ _
  · exact compiled_code 5 5 w _ h5 _
  · exact program_bound 5 5 w _ h5 _ _
  · exact compiled_code 5 6 w _ h6 _
  · exact program_bound 5 6 w _ h6 _ _
  · exact copy_bound w n hN

/-- Every read/write, including the PC test of each true loop, stays below
this allocation bound for all possible resident words. -/
theorem code_bound {w : ℕ} (hcap : 12≤2^w) (n K : ℕ) (hn : 0<n) (hk : 0<K)
    (hN : n≤2^w) (hK : K≤2^w) (r : ℕ) :
    BoundedCode (10+6*2^w) (TwoWordRadixSort.code hcap n K hn hk hN hK r) := by
  induction r with
  | zero => intro s hs; simp [TwoWordRadixSort.code] at hs
  | succ r ih =>
    intro s hs
    change s∈TwoWordRadixSort.code hcap n K hn hk hN hK r ++ _ at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ih s hs
    · exact round_bound hcap n K hn hk hN hK _ s hs

/-- Logarithmic-width keys give a fixed polynomial allocation. The exponent
2c depends only on the fixed word-width constant, never on input N. -/
theorem allocation_polynomial (N c w : ℕ) (hN : 2≤N) (hw : w≤c*Nat.clog 2 N) :
    10+6*2^w≤10+6*N^(2*c) := by
  have hp : 2^w≤N^(2*c) := by
    calc
      2^w≤2^(c*Nat.clog 2 N) := Nat.pow_le_pow_right (by decide) hw
      _=(2^Nat.clog 2 N)^c := by rw [←pow_mul,Nat.mul_comm c]
      _≤(N^2)^c := Nat.pow_le_pow_left (DirectRadix.ceiling_power_le_square N hN) c
      _=N^(2*c) := (pow_mul N 2 c).symm
  omega

end CSL.TwoWordRadixFootprint
end Footprint


