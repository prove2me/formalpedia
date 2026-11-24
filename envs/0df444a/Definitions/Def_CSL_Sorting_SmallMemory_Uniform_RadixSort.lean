-- Prove2me | Definitions.Def_CSL_Sorting_SmallMemory_Uniform_RadixSort
-- name    : CSL_Sorting_SmallMemory_Uniform_RadixSort
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:24:55.29914+00:00
-- url     : https://prove2.me/theorems/0eae8167-c3ec-469a-bdc0-53a42a7f7477
-- title:
--   Coded sorting library: Sorting / SmallMemory / Uniform / RadixSort
-- statement:
--   Module `CodedSorting.Sorting.SmallMemory.Uniform.RadixSort` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   A genuine fixed-table copy loop. The only public size parameter is the
--   initial last-position word. Three virtual instructions repeatedly load from
--   bank 5, store into bank 0, and decrement the disk-resident cursor. The loop
--   reads its PC from disk and halts at zero; no N-long command list is used.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.SmallMemory.Uniform.RadixSort

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_SmallMemory_Radix_Sort

section Copy
/-! A genuine fixed-table copy loop. The only public size parameter is the
initial last-position word. Three virtual instructions repeatedly load from
bank 5, store into bank 0, and decrement the disk-resident cursor. The loop
reads its PC from disk and halts at zero; no N-long command list is used. -/

set_option autoImplicit false
namespace CSL.TwoWordUniformCopy
open TwoWordSpill TwoWordIndirect TwoWordUniformLoop TwoWordRadixInsert

abbrev Logical (w : ℕ) := TwoWordIndirect.Logical (Fin 5) (Fin 6) (Word w)

def decrement {w : ℕ} (hcap : 11≤2^w) :
    TwoWordIndirect.Instruction (Fin 5) (Fin 6) (Word w) :=
  .arithmetic ⟨.inl 0,.inl 0,.inl 0,fun x _ => TwoWordRadixBuild.predecessor x,
    fun x _ => if x.val=0 then label hcap 3 else label hcap 0⟩

def table {w : ℕ} (hcap : 11≤2^w) :
    TwoWordIndirect.Table (Fin 5) (Fin 6) (Word w) :=
  [(label hcap 0,.load 5 0 1 (label hcap 1)),
   (label hcap 1,.store 0 0 1 (label hcap 2)),
   (label hcap 2,decrement hcap)]

def copyOne {w : ℕ} (hcap : 11≤2^w) (v : Logical w) : Logical w :=
  effect (decrement hcap)
    (storeEffect 0 0 1 (label hcap 2) (loadEffect 5 0 1 (label hcap 1) v))

theorem step_zero {w : ℕ} (hcap : 11≤2^w) (v : Logical w)
    (hp : v.pc=label hcap 0) :
    logicalStep (table hcap) v=loadEffect 5 0 1 (label hcap 1) v := by
  simp [logicalStep,table,tableEffect,hp,effect]

theorem step_one {w : ℕ} (hcap : 11≤2^w) (v : Logical w)
    (hp : v.pc=label hcap 1) :
    logicalStep (table hcap) v=storeEffect 0 0 1 (label hcap 2) v := by
  simp [logicalStep,table,tableEffect,hp,effect]

theorem step_two {w : ℕ} (hcap : 11≤2^w) (v : Logical w)
    (hp : v.pc=label hcap 2) :
    logicalStep (table hcap) v=effect (decrement hcap) v := by
  simp [logicalStep,table,tableEffect,hp,effect]

theorem copyOne_cursor {w : ℕ} (hcap : 11≤2^w) (v : Logical w) :
    (copyOne hcap v).regs (.inl 0)=TwoWordRadixBuild.predecessor (v.regs (.inl 0)) := by
  simp [copyOne,decrement,effect,applyInstruction,storeEffect,loadEffect]

theorem copyOne_pc {w : ℕ} (hcap : 11≤2^w) (v : Logical w) :
    (copyOne hcap v).pc=
      if (v.regs (.inl 0)).val=0 then label hcap 3 else label hcap 0 := by
  simp [copyOne,decrement,effect,applyInstruction,storeEffect,loadEffect]

theorem copyOne_data {w : ℕ} (hcap : 11≤2^w) (v : Logical w)
    (region : Fin 6) (x : Word w) :
    (copyOne hcap v).regs (.inr (region,x))=
      if region=0 ∧ x=v.regs (.inl 0) then v.regs (.inr (5,x))
      else v.regs (.inr (region,x)) := by
  by_cases hr : region=0 <;> by_cases hx : x=v.regs (.inl 0) <;>
    simp [copyOne,decrement,effect,applyInstruction,storeEffect,loadEffect,
      Function.update_apply,hr,hx]

theorem prepend_three {w : ℕ} (hcap : 11≤2^w) (v final : Logical w)
    (steps : ℕ) (hp : v.pc=label hcap 0)
    (hr : HaltsAfter (table hcap) (label hcap 3) steps (copyOne hcap v) final) :
    HaltsAfter (table hcap) (label hcap 3) (steps+3) v final := by
  have h1 : v.pc≠label hcap 3 := by rw [hp];simp
  have h2 : (loadEffect 5 0 1 (label hcap 1) v).pc=label hcap 1 := rfl
  have h3 : (storeEffect 0 0 1 (label hcap 2)
      (loadEffect 5 0 1 (label hcap 1) v)).pc=label hcap 2 := rfl
  change v.pc≠_ ∧ _
  refine ⟨h1,?_⟩
  rw [step_zero hcap v hp]
  refine ⟨by rw [h2];simp,?_⟩
  rw [step_one hcap _ h2]
  refine ⟨by rw [h3];simp,?_⟩
  rw [step_two hcap _ h3]
  exact hr

theorem copy_loop {w : ℕ} (hcap : 11≤2^w) (count : ℕ) (v : Logical w)
    (hp : v.pc=label hcap 0) (hc : (v.regs (.inl 0)).val=count) :
    ∃ final, HaltsAfter (table hcap) (label hcap 3) (3*(count+1)) v final ∧
      ∀ (region : Fin 6) (x : Word w), final.regs (.inr (region,x))=
        if region=0 ∧ x.val≤count then v.regs (.inr (5,x))
        else v.regs (.inr (region,x)) := by
  induction count generalizing v with
  | zero =>
      let final := copyOne hcap v
      have hstop : HaltsAfter (table hcap) (label hcap 3) 0 final final :=
        ⟨by rw [copyOne_pc,hc];rfl,rfl⟩
      refine ⟨final,prepend_three hcap v final 0 hp hstop,?_⟩
      intro region x
      rw [copyOne_data]
      have hx : x=v.regs (.inl 0) ↔ x.val≤0 := by rw [Fin.ext_iff,hc];omega
      simp only [hx]
  | succ count ih =>
      let next := copyOne hcap v
      have hpc : next.pc=label hcap 0 := by rw [copyOne_pc,hc];simp
      have hcur : (next.regs (.inl 0)).val=count := by
        rw [copyOne_cursor];simp [TwoWordRadixBuild.predecessor,hc]
      obtain ⟨final,hrun,hdata⟩ := ih next hpc hcur
      refine ⟨final,?_,?_⟩
      · convert prepend_three hcap v final (3*(count+1)) hp hrun using 1 <;> omega
      · intro region x
        rw [hdata,copyOne_data,copyOne_data]
        have hx : x=v.regs (.inl 0) ↔ x.val=count+1 := by rw [Fin.ext_iff,hc]
        simp only [hx]
        by_cases hr : region=0
        · by_cases hl : x.val≤count
          · simp [hr,hl,show x.val≤count+1 by omega]
          · by_cases he : x.val=count+1
            · simp [hr,hl,he]
            · simp [hr,hl,he,show ¬x.val≤count+1 by omega]
        · simp [hr]

theorem table_cost {w : ℕ} (hcap : 11≤2^w) : tableCost (table hcap)=24 := rfl
theorem table_length {w : ℕ} (hcap : 11≤2^w) : (table hcap).length=3 := rfl

theorem physical_loop {w : ℕ} (hcap : 11≤2^w) (count : ℕ)
    (s : TwoWordPhysicalAddresses.State (Word w))
    (hp : (view 5 6 w s).pc=label hcap 0)
    (hc : ((view 5 6 w s).regs (.inl 0)).val=count) :
    ∃ t, Physical.Executes (program 5 6 w (table hcap) (label hcap 3)) s t
      (78*(count+1)+1) ∧
      ∀ (region : Fin 6) (x : Word w), (view 5 6 w t).regs (.inr (region,x))=
        if region=0 ∧ x.val≤count then (view 5 6 w s).regs (.inr (5,x))
        else (view 5 6 w s).regs (.inr (region,x)) := by
  obtain ⟨final,hrun,hdata⟩ := copy_loop hcap count (view 5 6 w s) hp hc
  obtain ⟨t,ht,hv⟩ := terminates_of_source 5 6 w (table hcap) (label hcap 3) _ s final hrun
  refine ⟨t,?_,?_⟩
  · convert ht using 1 <;> rw [table_cost] <;> omega
  · rw [hv];exact hdata

def setupAbstract {w : ℕ} (hcap : 11≤2^w) (last : Word w) :
    List (TwoWordSpill.Command (TwoWordPhysicalAddresses.Register 5 6 w) (Word w)) :=
  [.localOp (fun _ => (last,label hcap 0)),
   .writeLeft (.reg (.inl 0)),.writeRight (fun _ => .pc)]

def setup {w : ℕ} (hcap : 11≤2^w) (last : Word w) :=
  (setupAbstract hcap last).map
    (TwoWordPhysicalAddresses.compile (TwoWordPhysicalAddresses.addressNumber 5 6 w))

def setupState {w : ℕ} (hcap : 11≤2^w) (last : Word w)
    (s : TwoWordPhysicalAddresses.State (Word w)) :=
  TwoWordPhysicalAddresses.execute (setup hcap last) s

theorem setup_cost {w : ℕ} (hcap : 11≤2^w) (last : Word w) :
    TwoWordPhysicalAddresses.transfers (setup hcap last)=2 := by
  rw [setup,TwoWordPhysicalAddresses.transfers_compile];rfl

theorem setup_view {w : ℕ} (hcap : 11≤2^w) (last : Word w)
    (s : TwoWordPhysicalAddresses.State (Word w)) :
    view 5 6 w (setupState hcap last s)=
      ⟨Function.update (view 5 6 w s).regs (.inl 0) last,label hcap 0⟩ := by
  unfold view setupState setup
  rw [TwoWordPhysicalAddresses.execute_pullback _
    (TwoWordPhysicalAddresses.addressNumber_injective 5 6 w)]
  simp [setupAbstract,TwoWordSpill.execute,TwoWordSpill.step,observe,resident]
  funext r
  simp [Function.update_apply]

def code {w : ℕ} (hcap : 12≤2^w) (n : ℕ) (hn : 0<n) (hN : n≤2^w) :
    List (TwoWordRadixPreparedBuild.Stage (Word w)) :=
  let cap := TwoWordRadixBuild.smallCap hcap
  [.straight (setup cap (position hN ⟨n-1,by omega⟩)),
   .loop (program 5 6 w (table cap) (label cap 3))]

def copyCost (n : ℕ) := 78*n+3

theorem physical_copy {w : ℕ} (hcap : 12≤2^w) (n : ℕ) (hn : 0<n) (hN : n≤2^w)
    (s : TwoWordPhysicalAddresses.State (Word w)) :
    ∃ t, TwoWordRadixPreparedBuild.Executes (code hcap n hn hN) s t (copyCost n) ∧
      (∀ j : Fin n, t.disk (5+j.val)=s.disk (5+5*2^w+j.val)) ∧
      (∀ (region : Fin 6) (x : Word w), region≠0 →
        (view 5 6 w t).regs (.inr (region,x))=(view 5 6 w s).regs (.inr (region,x))) := by
  let cap := TwoWordRadixBuild.smallCap hcap
  let last := position hN (⟨n-1,by omega⟩ : Fin n)
  let ready := setupState cap last s
  have hp : (view 5 6 w ready).pc=label cap 0 := by rw [setup_view]
  have hc : ((view 5 6 w ready).regs (.inl 0)).val=n-1 := by
    rw [setup_view];simp [last,position]
  obtain ⟨t,ht,hd⟩ := physical_loop cap (n-1) ready hp hc
  have hdata (region : Fin 6) (x : Word w) :
      (view 5 6 w ready).regs (.inr (region,x))=(view 5 6 w s).regs (.inr (region,x)) := by
    rw [setup_view];simp
  refine ⟨t,?_,?_,?_⟩
  · have hall := TwoWordRadixPreparedBuild.Executes.straight (setup cap last) _ s t _
      (TwoWordRadixPreparedBuild.Executes.loop _ [] ready t t _ 0 ht
        (TwoWordRadixPreparedBuild.Executes.done t))
    convert hall using 1
    all_goals first | rfl | (rw [setup_cost]; unfold copyCost; omega)
  · intro j
    have h := hd 0 (position hN j)
    rw [if_pos (by simp [position];omega),hdata] at h
    rw [TwoWordRadixPass.view_data_address,TwoWordRadixPass.view_data_address] at h
    change t.disk (5+0*2^w+j.val)=s.disk (5+5*2^w+j.val) at h
    simpa only [Nat.zero_mul,Nat.add_zero] using h
  · intro region x hr
    rw [hd,if_neg (by simp [hr]),hdata]

theorem code_bound {w : ℕ} (hcap : 12≤2^w) (n : ℕ) (hn : 0<n) (hN : n≤2^w) :
    TwoWordRadixFootprint.BoundedCode (10+6*2^w) (code hcap n hn hN) := by
  have hb : 5+6*2^w+5≤10+6*2^w := by omega
  intro st hs
  simp only [code,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl
  · exact TwoWordRadixFootprint.compiled_code 5 6 w _ hb _
  · exact TwoWordRadixFootprint.program_bound 5 6 w _ hb _ _

end CSL.TwoWordUniformCopy
end Copy

section RadixSort
/-! Complete fixed-loop radix sorting. Every pass includes the actual
linked-directory traversal and the actual fixed-table copy loop. The stage
count is 10 per public digit round and is independent of the input length.
Finite addresses use the original word width; no word enlargement occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CSL.TwoWordUniformRadixSort
open TwoWordRadixInsert TwoWordRadixPreparedBuild
open TwoWordPhysicalAddresses (State)
open TwoWordRadixSort (File digit output output_length output_perm output_sorted)

def roundCode {w : ℕ} (hcap : 12≤2^w) (n K : ℕ) (hn : 0<n) (hk : 0<K)
    (hN : n≤2^w) (hK : K≤2^w) (key : Word w → Fin K) : List (Stage (Word w)) :=
  TwoWordRadixPass.code hcap (position hK ⟨K-1,by omega⟩)
    (position hN ⟨n-1,by omega⟩) (fun x => position hK (key x)) ++
  TwoWordUniformCopy.code hcap n hn hN

theorem round_correct {w : ℕ} (hcap : 12≤2^w) (n K : ℕ) (hn : 0<n) (hk : 0<K)
    (hN : n≤2^w) (hK : K≤2^w) (key : Word w → Fin K)
    (s : State (Word w)) (xs : List (Word w)) (hlen : xs.length=n) (hin : File s xs) :
    ∃ t, Executes (roundCode hcap n K hn hk hN hK key) s t (1605*n+376*K+96) ∧
      File t (BucketMachine.collect key xs) := by
  subst n
  obtain ⟨t,ht,_,hout⟩ := TwoWordRadixPass.physical_pass_disk hcap hK hk xs hn hN key s hin
  obtain ⟨t',hc,hcopy,_⟩ := TwoWordUniformCopy.physical_copy hcap xs.length hn hN t
  refine ⟨t',?_,?_⟩
  · have he := TwoWordRadixPass.executes_append ht hc
    convert he using 1
    all_goals first | rfl | (unfold TwoWordUniformCopy.copyCost; omega)
  · intro j
    have hj : j.val<xs.length := by simpa only [BucketMachine.collect_length] using j.isLt
    exact (hcopy ⟨j.val,hj⟩).trans (hout j.val j.isLt)

def code {w : ℕ} (hcap : 12≤2^w) (n K : ℕ) (hn : 0<n) (hk : 0<K)
    (hN : n≤2^w) (hK : K≤2^w) : ℕ → List (Stage (Word w))
  | 0 => []
  | r+1 => code hcap n K hn hk hN hK r ++
      roundCode hcap n K hn hk hN hK (digit K hk r)

/-- Exact cost and exact final data refer to this one complete physical run. -/
theorem physical_sort {w : ℕ} (hcap : 12≤2^w) (n K : ℕ) (hn : 0<n) (hk : 0<K)
    (hN : n≤2^w) (hK : K≤2^w) (r : ℕ) (s : State (Word w))
    (xs : List (Word w)) (hlen : xs.length=n) (hin : File s xs) :
    ∃ t, Executes (code hcap n K hn hk hN hK r) s t (r*(1605*n+376*K+96)) ∧
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
      s t ((2*c)*(1981*xs.length+96)) ∧
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


/-- Ten stages per digit: all input-length iteration happens inside genuine
PC-tested while loops, not inside an N-long straight-line schedule. -/
theorem code_length {w : ℕ} (hcap : 12≤2^w) (n K : ℕ) (hn : 0<n) (hk : 0<K)
    (hN : n≤2^w) (hK : K≤2^w) (r : ℕ) :
    (code hcap n K hn hk hN hK r).length=10*r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (code hcap n K hn hk hN hK r ++ _).length=10*(r+1)
    rw [List.length_append,ih]
    simp only [roundCode,TwoWordRadixPass.code,TwoWordRadixPreparedBuild.code,
      TwoWordUniformCopy.code,List.length_append,List.length_cons,List.length_nil]
    omega

theorem code_bound {w : ℕ} (hcap : 12≤2^w) (n K : ℕ) (hn : 0<n) (hk : 0<K)
    (hN : n≤2^w) (hK : K≤2^w) (r : ℕ) :
    TwoWordRadixFootprint.BoundedCode (10+6*2^w) (code hcap n K hn hk hN hK r) := by
  induction r with
  | zero => intro st hs; simp [code] at hs
  | succ r ih =>
    intro st hs
    change st∈code hcap n K hn hk hN hK r ++ _ at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ih st hs
    · change st∈TwoWordRadixPass.code _ _ _ _ ++ _ at hs
      rcases List.mem_append.mp hs with hs | hs
      · apply TwoWordRadixFootprint.round_bound hcap n K hn hk hN hK _ st
        exact List.mem_append_left _ hs
      · exact TwoWordUniformCopy.code_bound hcap n hn hN st hs

end CSL.TwoWordUniformRadixSort
end RadixSort


