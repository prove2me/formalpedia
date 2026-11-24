-- Prove2me | Definitions.Def_CSL_Shared_Memory_ProgramWorkspace
-- name    : CSL_Shared_Memory_ProgramWorkspace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:19:56.021585+00:00
-- url     : https://prove2.me/theorems/db24e663-bf65-4c59-8035-cc63c3a5cc49
-- title:
--   Coded sorting library: Shared / Memory / ProgramWorkspace
-- statement:
--   Module `CodedSorting.Shared.Memory.ProgramWorkspace` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   A block-addressed, append-only allocator. Reservation slack costs no
--   I/O: only the blocks explicitly written by a primitive are touched.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.ProgramWorkspace

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Memory_PolynomialWorkspace
import Definitions.Def_CSL_Shared_Words_WordConvention
import Definitions.Def_CSL_Interchange_Framework_Recursion_RecursiveExchangeCost

section WorkspaceAllocation
/-! A block-addressed, append-only allocator. Reservation slack costs no
I/O: only the blocks explicitly written by a primitive are touched. -/
namespace CSL.WorkspaceAllocation

structure Span where
  start : ℕ
  blocks : ℕ
  deriving DecidableEq, Repr

def Span.stop (s : Span) := s.start+s.blocks
def Span.Contains (s : Span) (address : ℕ) := s.start≤address ∧ address<s.stop
def Before (left right : Span) := left.stop≤right.start

/-- Allocation advances one public pointer using the supplied file-length
descriptors. It never reads payload blocks. -/
def allocate (next : ℕ) : List ℕ→List Span
  | [] => []
  | n::rest => ⟨next,n⟩::allocate (next+n) rest

theorem allocate_lengths (next : ℕ) (sizes : List ℕ) :
    (allocate next sizes).map Span.blocks=sizes := by
  induction sizes generalizing next with
  | nil => rfl
  | cons n rest ih => simp [allocate,ih]

theorem allocate_bounds (next : ℕ) (sizes : List ℕ) (s : Span)
    (hs : s∈allocate next sizes) : next≤s.start ∧ s.stop≤next+sizes.sum := by
  induction sizes generalizing next with
  | nil => simp [allocate] at hs
  | cons n rest ih =>
    simp only [allocate,List.mem_cons] at hs
    rcases hs with rfl|hs
    · simp only [Span.stop,List.sum_cons]; omega
    · have h := ih (next+n) hs
      simp only [List.sum_cons]
      omega

theorem allocate_pairwise (next : ℕ) (sizes : List ℕ) :
    (allocate next sizes).Pairwise Before := by
  induction sizes generalizing next with
  | nil => simp [allocate]
  | cons n rest ih =>
    simp only [allocate,List.pairwise_cons]
    exact ⟨fun s hs => (allocate_bounds (next+n) rest s hs).1,ih _⟩

theorem before_no_alias {left right : Span} (h : Before left right) (a : ℕ)
    (hl : left.Contains a) : ¬right.Contains a := by
  unfold Before Span.Contains Span.stop at *
  omega

/-- Distinct file identifiers, including parent versus child files, have
disjoint block intervals in the actual allocation list. -/
theorem allocate_distinct_order (next : ℕ) (sizes : List ℕ)
    (i j : Fin (allocate next sizes).length) (hij : i≠j) :
    Before ((allocate next sizes).get i) ((allocate next sizes).get j) ∨
      Before ((allocate next sizes).get j) ((allocate next sizes).get i) := by
  have h := List.pairwise_iff_get.mp (allocate_pairwise next sizes)
  rcases lt_or_gt_of_ne hij with hij|hij
  · exact Or.inl (h i j hij)
  · exact Or.inr (h j i hij)

theorem allocate_addresses (next : ℕ) (sizes : List ℕ) (s : Span)
    (hs : s∈allocate next sizes) (a : ℕ) (ha : s.Contains a) :
    next≤a ∧ a<next+sizes.sum := by
  have h := allocate_bounds next sizes s hs
  unfold Span.Contains at ha
  omega

section Writes
open WordControl
variable {B w : ℕ}

/-- One actual block write, using the existing block-machine operation. -/
def writeAt (s : Span) (i : Fin s.blocks) (buffer : Fin B→Word w)
    (disk : BlockDisk B w) : BlockDisk B w :=
  writeBlock disk (s.start+i.val) buffer

theorem writeAt_target (s : Span) (i : Fin s.blocks) (buffer : Fin B→Word w)
    (disk : BlockDisk B w) : writeAt s i buffer disk (s.start+i.val)=buffer := by
  simp [writeAt,writeBlock]

theorem writeAt_outside (s : Span) (i : Fin s.blocks) (buffer : Fin B→Word w)
    (disk : BlockDisk B w) (a : ℕ) (ha : ¬s.Contains a) :
    writeAt s i buffer disk a=disk a := by
  have hne : a≠s.start+i.val := by
    intro h
    apply ha
    subst a
    unfold Span.Contains Span.stop
    exact ⟨by omega,by have hi := i.isLt; omega⟩
  simp [writeAt,writeBlock,hne]

/-- A primitive may fill only a prefix of a reserved file. Each operation
uses one block buffer; unused reservation slack is never read or written. -/
def writePrefix (s : Span) (produce : Fin s.blocks→Fin B→Word w) :
    (n : ℕ)→n≤s.blocks→BlockDisk B w→BlockDisk B w
  | 0,_,disk => disk
  | n+1,hn,disk => writePrefix s produce n (by omega)
      (writeAt s ⟨n,by omega⟩ (produce ⟨n,by omega⟩) disk)

theorem writePrefix_outside (s : Span) (produce : Fin s.blocks→Fin B→Word w)
    (n : ℕ) (hn : n≤s.blocks) (disk : BlockDisk B w) (a : ℕ) (ha : ¬s.Contains a) :
    writePrefix s produce n hn disk a=disk a := by
  induction n generalizing disk with
  | zero => rfl
  | succ n ih =>
    rw [writePrefix,ih]
    exact writeAt_outside s _ _ disk a ha

/-- No operation visits an address beyond the prefix actually filled. -/
theorem writePrefix_untouched (s : Span) (produce : Fin s.blocks→Fin B→Word w)
    (n : ℕ) (hn : n≤s.blocks) (disk : BlockDisk B w) (a : ℕ)
    (ha : a<s.start ∨ s.start+n≤a) :
    writePrefix s produce n hn disk a=disk a := by
  induction n generalizing disk with
  | zero => rfl
  | succ n ih =>
    rw [writePrefix,ih _ _ (by omega)]
    simp only [writeAt,writeBlock,if_neg (show a≠s.start+n by omega)]

/-- Filled blocks contain exactly the primitive's produced blocks. The
proof follows each physical one-block write, not an assumed whole-file copy. -/
theorem writePrefix_at (s : Span) (produce : Fin s.blocks→Fin B→Word w)
    (n : ℕ) (hn : n≤s.blocks) (disk : BlockDisk B w) (i : Fin s.blocks) (hi : i.val<n) :
    writePrefix s produce n hn disk (s.start+i.val)=produce i := by
  induction n generalizing disk with
  | zero => omega
  | succ n ih =>
    rw [writePrefix]
    by_cases h : i.val<n
    · exact ih _ _ h
    · have he : i.val=n := by omega
      rw [writePrefix_untouched s produce n _ _ _ (Or.inr (by omega))]
      have hi' : i=⟨n,by omega⟩ := Fin.ext he
      rw [hi']
      exact writeAt_target s _ _ disk

theorem writePrefix_preserves_other (left right : Span) (h : Before left right ∨ Before right left)
    (produce : Fin left.blocks→Fin B→Word w) (n : ℕ) (hn : n≤left.blocks)
    (disk : BlockDisk B w) (a : ℕ) (ha : right.Contains a) :
    writePrefix left produce n hn disk a=disk a := by
  apply writePrefix_outside
  intro hl
  rcases h with h|h
  · exact before_no_alias h a hl ha
  · exact before_no_alias h a ha hl

/-- Instantiation at actual allocated identifiers: filling one primitive's
file cannot modify a source, sibling, ancestor, or descendant file. -/
theorem allocated_write_preserves_other (next : ℕ) (sizes : List ℕ)
    (i j : Fin (allocate next sizes).length) (hij : i≠j)
    (produce : Fin ((allocate next sizes).get i).blocks→Fin B→Word w)
    (n : ℕ) (hn : n≤((allocate next sizes).get i).blocks)
    (disk : BlockDisk B w) (a : ℕ) (ha : ((allocate next sizes).get j).Contains a) :
    writePrefix ((allocate next sizes).get i) produce n hn disk a=disk a :=
  writePrefix_preserves_other _ _ (allocate_distinct_order next sizes i j hij)
    produce n hn disk a ha

end Writes


/-- A packed V-record file always fits the deliberately coarse V-block
reservation, including V=0. Slack blocks need no initialization. -/
theorem packed_file_fits {α : Type*} (B : ℕ) (hB : 0<B) (xs : List α) :
    (BucketMachine.pack B hB xs).length≤xs.length := by
  have h := (BucketMachine.pack_capacity B hB xs).2
  have hn : xs.length≤xs.length*B := Nat.le_mul_of_pos_right _ hB
  by_contra hbad
  have hm := Nat.mul_le_mul_right B
    (show xs.length+1≤(BucketMachine.pack B hB xs).length by omega)
  nlinarith

noncomputable section
namespace Exchange
open RecursiveExchange
open PolynomialWorkspace.Exchange
open scoped BigOperators

/-- Each local file receives V *blocks*, even though a packed V-record file
needs only ceil(V/B) blocks. The unused gaps simplify allocation without
adding any transfer. Child lists are indexed by the real edge/pivot type. -/
def fileSizes (C : ℕ) : CallTree→List ℕ
  | .stop _ V _ => List.replicate C V
  | .level _ V _ children => List.replicate C V++
      (Finset.univ : Finset Child).toList.flatMap (fun c => fileSizes C (children c))

private theorem sum_flatMap_eq {α : Type*} (xs : List α) (f : α→List ℕ) :
    (xs.flatMap f).sum=(xs.map (fun a => (f a).sum)).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih => simp [ih]

theorem fileSizes_sum (C : ℕ) (tree : CallTree) :
    (fileSizes C tree).sum=reservation C tree := by
  induction tree with
  | stop width V charge => simp [fileSizes,reservation]
  | level width V charge children ih =>
    simp only [fileSizes,List.sum_append,List.sum_replicate,smul_eq_mul,
      sum_flatMap_eq,Function.comp_def,ih,Finset.sum_map_toList,reservation]

/-- These are the actual sequentially allocated spans for every local file
of every invocation, including all descendants. -/
def files (C : ℕ) (tree : CallTree) := allocate 0 (fileSizes C tree)

theorem files_pairwise (C : ℕ) (tree : CallTree) : (files C tree).Pairwise Before :=
  allocate_pairwise _ _

theorem files_capacity (C : ℕ) (tree : CallTree) :
    ((files C tree).map Span.blocks).sum=reservation C tree := by
  rw [files,allocate_lengths,fileSizes_sum]

/-- Every block address actually handed out by the allocator is below the
proved polynomial for the true cutoffExchange tree. -/
theorem actual_address_bound (C base cutoff k rows : ℕ) (hb : 0<base)
    (leaf : ℕ→ℕ) (charge : ℕ→ℕ→ℕ)
    {P G Z : Type} [Fintype P] [Fintype G] [Fintype Z]
    (layout : P ≃ Fin (rows*Parameters.W^k))
    (hV : 0<Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z))
    (file : Span)
    (hf : file∈files C (cutoffExchange base cutoff leaf charge k rows (Gap := G) (Suffix := Z) layout).calls)
    (a : ℕ) (ha : file.Contains a) :
    a<(Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z))^
      (Nat.clog 2 C+2*Nat.clog radix (Parameters.S+1)+1) := by
  have h := (allocate_addresses 0 _ file hf a ha).2
  rw [Nat.zero_add,fileSizes_sum] at h
  exact h.trans_le (cutoff_integer_polynomial C base cutoff k rows hb leaf charge layout hV)

/-- Bases, lengths and one-past-end pointers are bounded even for empty
file reservations. This is the descriptor interface for the stack codec. -/
theorem actual_span_bound (C base cutoff k rows : ℕ) (hb : 0<base)
    (leaf : ℕ→ℕ) (charge : ℕ→ℕ→ℕ)
    {P G Z : Type} [Fintype P] [Fintype G] [Fintype Z]
    (layout : P ≃ Fin (rows*Parameters.W^k))
    (hV : 0<Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z))
    (file : Span)
    (hf : file∈files C (cutoffExchange base cutoff leaf charge k rows (Gap := G) (Suffix := Z) layout).calls) :
    let V := Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)
    let e := Nat.clog 2 C+2*Nat.clog radix (Parameters.S+1)+1
    file.start≤V^e ∧ file.blocks≤V^e ∧ file.stop≤V^e := by
  try dsimp only
  have h := (allocate_bounds 0 _ file hf).2
  rw [Nat.zero_add,fileSizes_sum] at h
  have hp := h.trans (cutoff_integer_polynomial C base cutoff k rows hb leaf charge layout hV)
  unfold Span.stop at *
  omega

/-- Convert any polynomial root-volume bound into the global input-size
bound used by WordControl; no change of global word size is made. -/
theorem span_global_bound (s : Span) (V N exponent volumeExponent : ℕ)
    (hs : s.stop≤V^exponent) (hV : V≤N^volumeExponent) :
    s.start≤N^(volumeExponent*exponent) ∧ s.blocks≤N^(volumeExponent*exponent) ∧
      s.stop≤N^(volumeExponent*exponent) := by
  have h := hs.trans (Nat.pow_le_pow_left hV exponent)
  rw [←pow_mul] at h
  unfold Span.stop at *
  omega

/-- The public block pointer is a concrete fixed tuple of global words.
The exponent depends only on the fixed circuit and the static slot count. -/
def addressWords (V w exponent : ℕ) (hV : 2≤V) (hw : Nat.clog 2 V≤w)
    (address : ℕ) (haddress : address<V^exponent) :
    WordControl.Words (exponent+1) w :=
  WordControl.encodeCounter V w exponent hV hw ⟨address,by omega⟩

@[simp] theorem addressWords_decode (V w exponent : ℕ) (hV : 2≤V) (hw : Nat.clog 2 V≤w)
    (address : ℕ) (haddress : address<V^exponent) :
    WordControl.decodeWords (addressWords V w exponent hV hw address haddress)=address := by
  simp only [addressWords,WordControl.decode_encodeCounter]

end Exchange
end
end CSL.WorkspaceAllocation
end WorkspaceAllocation

section AllocatedFileMachine
/-! Relocating a bounded family of external files to one physical disk.

Every file-local read/write translates to one physical block operation, with
the same resident banks and exact transfer count. Distinct allocated spans
cannot alias. This is a simulation for a fixed allocation and fixed policy;
it does not instantiate the complete recursive algorithm's file family or
prove that its descriptors and controller fit the final RAM budget.
-/

set_option autoImplicit false
namespace CSL.AllocatedFileMachine
open WorkspaceAllocation

abbrev Address (spans : List Span) :=
  (file : Fin spans.length) × Fin (spans.get file).blocks

def address {spans : List Span} (a : Address spans) : ℕ :=
  (spans.get a.1).start+a.2.val

theorem address_contains {spans : List Span} (a : Address spans) :
    (spans.get a.1).Contains (address a) := by
  have h := a.2.isLt
  simp only [Span.Contains,Span.stop,address]
  omega

theorem address_injective {spans : List Span} (h : spans.Pairwise Before) :
    Function.Injective (@address spans) := by
  intro a b he
  have hf : a.1=b.1 := by
    by_contra hn
    have hp := List.pairwise_iff_get.mp h
    rcases lt_or_gt_of_ne hn with hab|hba
    · exact before_no_alias (hp a.1 b.1 hab) (address a)
        (address_contains a) (he ▸ address_contains b)
    · exact before_no_alias (hp b.1 a.1 hba) (address b)
        (address_contains b) (he ▸ address_contains a)
  rcases a with ⟨i,a⟩
  rcases b with ⟨j,b⟩
  try dsimp only at hf
  subst j
  have hv : a.val=b.val := by simpa only [address,Nat.add_left_cancel_iff] using he
  cases Fin.ext hv
  rfl

theorem allocated_address_bound (start : ℕ) (sizes : List ℕ)
    (a : Address (allocate start sizes)) :
    start ≤ address a ∧ address a < start+sizes.sum :=
  allocate_addresses start sizes _ (List.get_mem _ _) _ (address_contains a)

variable {Bank : Type*} {R : ℕ} {spans : List Span}

structure State (Bank : Type*) (R : ℕ) (spans : List Span) where
  ram : Fin R → Bank
  files : Address spans → Bank

inductive Operation (Bank : Type*) (R : ℕ) (spans : List Span) where
  | read (block : Address spans) (bank : Fin R)
  | write (block : Address spans) (bank : Fin R)
  | cpu (f : (Fin R → Bank) → (Fin R → Bank))

def cost : Operation Bank R spans → ℕ
  | .read _ _ => 1
  | .write _ _ => 1
  | .cpu _ => 0

def step (op : Operation Bank R spans) (s : State Bank R spans) : State Bank R spans :=
  match op with
  | .read a r => ⟨Function.update s.ram r (s.files a),s.files⟩
  | .write a r => ⟨s.ram,Function.update s.files a (s.ram r)⟩
  | .cpu f => ⟨f s.ram,s.files⟩

def translate : Operation Bank R spans → BitWordPacking.Operation Bank R
  | .read a r => .read (address a) r
  | .write a r => .write (address a) r
  | .cpu f => .cpu f

@[simp] theorem translate_cost (op : Operation Bank R spans) :
    BitWordPacking.transferCost (translate op)=cost op := by cases op <;> rfl

def Represents (localState : State Bank R spans) (physical : BitWordPacking.State Bank R) : Prop :=
  physical.ram=localState.ram ∧ ∀ a,physical.disk (address a)=localState.files a

theorem step_represents (hspans : spans.Pairwise Before)
    (op : Operation Bank R spans) (s : State Bank R spans)
    (p : BitWordPacking.State Bank R) (hp : Represents s p) :
    Represents (step op s) (BitWordPacking.step (translate op) p) := by
  rcases hp with ⟨hr,hf⟩
  cases op with
  | read a r =>
    exact ⟨by simp only [step,translate,BitWordPacking.step,hr,hf],hf⟩
  | write a r =>
    refine ⟨hr,?_⟩
    intro b
    by_cases hb : b=a
    · subst b
      simp [step,translate,BitWordPacking.step,hr]
    · have hn : address b ≠ address a := fun h => hb (address_injective hspans h)
      simpa only [step,translate,BitWordPacking.step,Function.update_of_ne hb,
        Function.update_of_ne hn] using hf b
  | cpu f => exact ⟨congrArg f hr,hf⟩

/-- Instructions are chosen afresh from resident banks. No selected
instruction or file contents occur as an extra state field. -/
abbrev Policy (Bank : Type*) (R : ℕ) (spans : List Span) :=
  (Fin R → Bank) → Option (Operation Bank R spans)

def run (policy : Policy Bank R spans) : ℕ → State Bank R spans → State Bank R spans × ℕ
  | 0,s => (s,0)
  | fuel+1,s => match policy s.ram with
    | none => (s,0)
    | some op =>
      let rest := run policy fuel (step op s)
      (rest.1,cost op+rest.2)

def translatePolicy (policy : Policy Bank R spans) : BitWordPacking.Policy Bank R :=
  fun ram => (policy ram).map translate

/-- The same fixed policy works for every initial payload satisfying the
representation relation. No new physical program is chosen from the input. -/
theorem run_represents (hspans : spans.Pairwise Before)
    (policy : Policy Bank R spans) (fuel : ℕ)
    (s : State Bank R spans) (p : BitWordPacking.State Bank R)
    (hp : Represents s p) :
    Represents (run policy fuel s).1
      (BitWordPacking.run (translatePolicy policy) fuel p).1 ∧
      (BitWordPacking.run (translatePolicy policy) fuel p).2=(run policy fuel s).2 := by
  induction fuel generalizing s p with
  | zero => exact ⟨hp,rfl⟩
  | succ fuel ih =>
    have hpolicy : translatePolicy policy p.ram=(policy s.ram).map translate := by
      rw [translatePolicy,hp.1]
    cases hs : policy s.ram with
    | none => simpa only [run,hs,BitWordPacking.run,hpolicy,Option.map] using (show Represents s p ∧ (0 : ℕ)=0 from ⟨hp,rfl⟩)
    | some op =>
      have hnext := step_represents hspans op s p hp
      have ht := ih (step op s) (BitWordPacking.step (translate op) p) hnext
      simpa only [run,hs,BitWordPacking.run,hpolicy,Option.map,translate_cost] using
        And.intro ht.1 (congrArg (fun n => cost op+n) ht.2)

theorem step_outside (op : Operation Bank R spans) (p : BitWordPacking.State Bank R)
    (a : ℕ) (ha : ∀ b : Address spans,address b≠a) :
    (BitWordPacking.step (translate op) p).disk a=p.disk a := by
  cases op with
  | read => rfl
  | cpu => rfl
  | write b r =>
    simp only [translate,BitWordPacking.step,Function.update_of_ne (Ne.symm (ha b))]

/-- Running the program cannot change unallocated blocks, even when writes
and later reads revisit the same file dynamically. -/
theorem run_outside (policy : Policy Bank R spans) (fuel : ℕ)
    (p : BitWordPacking.State Bank R) (a : ℕ)
    (ha : ∀ b : Address spans,address b≠a) :
    (BitWordPacking.run (translatePolicy policy) fuel p).1.disk a=p.disk a := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
    cases hs : policy p.ram with
    | none => simp [BitWordPacking.run,translatePolicy,hs]
    | some op =>
      simp only [BitWordPacking.run,translatePolicy,hs,Option.map_some]
      exact (ih _).trans (step_outside op p a ha)

/-- Direct instantiation by the append-only allocator, with exact I/O
preservation and no storage outside its reserved interval modified. -/
theorem allocated_run (start : ℕ) (sizes : List ℕ)
    (policy : Policy Bank R (allocate start sizes)) (fuel : ℕ)
    (s : State Bank R (allocate start sizes)) (p : BitWordPacking.State Bank R)
    (hp : Represents s p) :
    Represents (run policy fuel s).1
      (BitWordPacking.run (translatePolicy policy) fuel p).1 ∧
      (BitWordPacking.run (translatePolicy policy) fuel p).2=(run policy fuel s).2 ∧
      ∀ a,a<start ∨ start+sizes.sum≤a →
        (BitWordPacking.run (translatePolicy policy) fuel p).1.disk a=p.disk a := by
  obtain ⟨hr,hc⟩ := run_represents (allocate_pairwise start sizes) policy fuel s p hp
  refine ⟨hr,hc,?_⟩
  intro a ha
  apply run_outside
  intro b hb
  have h := allocated_address_bound start sizes b
  omega

/-- A bit-stream block contains exactly B*w bits. Relocation followed by
the position-preserving word codec gives the same run on B-word blocks,
without an extra disk pass or a changed transfer count. -/
theorem allocated_bit_run_word {B w : ℕ} (start : ℕ) (sizes : List ℕ)
    (policy : Policy (Fin (B*w) → Circuit.Bit) R (allocate start sizes)) (fuel : ℕ)
    (s : State (Fin (B*w) → Circuit.Bit) R (allocate start sizes))
    (p : BitWordPacking.State (Fin B → WordControl.Word w) R)
    (hp : Represents s (BitWordPacking.mapState (BitWordPacking.blockBits B w) p)) :
    let wordRun := BitWordPacking.run
      (BitWordPacking.mapPolicy (BitWordPacking.blockBits B w).symm (translatePolicy policy)) fuel p
    Represents (run policy fuel s).1
      (BitWordPacking.mapState (BitWordPacking.blockBits B w) wordRun.1) ∧
      wordRun.2=(run policy fuel s).2 := by
  obtain ⟨hr,hc⟩ := run_represents (allocate_pairwise start sizes) policy fuel s
    (BitWordPacking.mapState (BitWordPacking.blockBits B w) p) hp
  have hsim := BitWordPacking.run_map (BitWordPacking.blockBits B w).symm
    (translatePolicy policy) fuel (BitWordPacking.mapState (BitWordPacking.blockBits B w) p)
  rw [BitWordPacking.mapState_inverse] at hsim
  try dsimp only
  rw [hsim]
  have hundo (x : BitWordPacking.State (Fin (B*w) → Circuit.Bit) R) :
      BitWordPacking.mapState (BitWordPacking.blockBits B w)
        (BitWordPacking.mapState (BitWordPacking.blockBits B w).symm x)=x := by
    cases x
    simp [BitWordPacking.mapState,BitWordPacking.mapRAM,Function.comp_def]
  rw [hundo]
  exact ⟨hr,hc⟩

/-- Physical block pointers fit a fixed tuple of the original global
words whenever the allocated interval has the stated polynomial bound.
This does not enlarge the word width or claim the entire controller fits. -/
def allocatedAddressWords {N exponent w : ℕ} (hN : 2≤N) (hw : Nat.clog 2 N≤w)
    (start : ℕ) (sizes : List ℕ) (hcapacity : start+sizes.sum≤N^exponent)
    (a : Address (allocate start sizes)) : WordControl.Words (exponent+1) w :=
  WorkspaceAllocation.Exchange.addressWords N w exponent hN hw (address a)
    ((allocated_address_bound start sizes a).2.trans_le hcapacity)

@[simp] theorem allocatedAddressWords_decode {N exponent w : ℕ}
    (hN : 2≤N) (hw : Nat.clog 2 N≤w)
    (start : ℕ) (sizes : List ℕ) (hcapacity : start+sizes.sum≤N^exponent)
    (a : Address (allocate start sizes)) :
    WordControl.decodeWords (allocatedAddressWords hN hw start sizes hcapacity a)=address a :=
  WorkspaceAllocation.Exchange.addressWords_decode N w exponent hN hw (address a) _

end CSL.AllocatedFileMachine
end AllocatedFileMachine

section ProgramWorkspace
/-! File allocation for primitive instruction lists. The caller supplies the source files; each pass allocates its output files, which become inputs to the following pass. 

-/
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 4096
namespace CSL.ProgramWorkspace
open ScanProgram RecursiveExchange RecursiveExchangeCost
open scoped BigOperators
noncomputable section

def Pass.newFiles {V : ℕ} : ScanProgram.Pass V→ℕ
  | .streams K _ _ _ => K+1
  | .reverse _ _ _ _ => 1

/-- A stream pass has one file per bucket and one result file. A reflection
has a single result file. No reuse is needed for this coarse allocation. -/
abbrev PassSlot {V : ℕ} (p : ScanProgram.Pass V) := Fin (Pass.newFiles p)
abbrev ProgramSlot {V : ℕ} (ps : List (ScanProgram.Pass V)) :=
  (i : Fin ps.length) × PassSlot (ps.get i)

theorem pass_file_bound {V : ℕ} (p : ScanProgram.Pass V) :
    Pass.newFiles p≤p.constant := by
  cases p with
  | streams => simp only [Pass.newFiles,ScanProgram.Pass.constant]; omega
  | reverse => norm_num [Pass.newFiles,ScanProgram.Pass.constant]

theorem program_slot_count {V : ℕ} (ps : List (ScanProgram.Pass V)) :
    Fintype.card (ProgramSlot ps)=(ps.map Pass.newFiles).sum := by
  simp only [ProgramSlot,Fintype.card_sigma,Fintype.card_fin]
  rw [←List.sum_ofFn]
  change (List.ofFn (Pass.newFiles ∘ ps.get)).sum=_
  rw [←List.map_ofFn,List.ofFn_get]

theorem program_slot_bound {V : ℕ} (ps : List (ScanProgram.Pass V)) :
    Fintype.card (ProgramSlot ps)≤totalConstant ps := by
  simp only [ProgramSlot,Fintype.card_sigma,Fintype.card_fin]
  have h := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => pass_file_bound (ps.get i))
  have he : (∑ i : Fin ps.length,(ps.get i).constant)=totalConstant ps := by
    rw [←List.sum_ofFn]
    change (List.ofFn (ScanProgram.Pass.constant ∘ ps.get)).sum=_
    rw [←List.map_ofFn,List.ofFn_get]
    rfl
  exact h.trans_eq he

/-- An injective assignment of every named pass/bucket/output file to a
fixed budget. The bound comes from the actual pass list's proven constant. -/
def programSlotIndex {V : ℕ} (ps : List (ScanProgram.Pass V)) (budget : ℕ)
    (hbudget : totalConstant ps≤budget) : ProgramSlot ps↪Fin budget where
  toFun slot := ((Fintype.equivFin (ProgramSlot ps)) slot).castLE ((program_slot_bound ps).trans hbudget)
  inj' x y h := by
    apply (Fintype.equivFin (ProgramSlot ps)).injective
    apply Fin.ext
    simpa only [Fin.coe_castLE] using congrArg (@Fin.val budget) h

/-- All four real factor programs at all physical edges. -/
abbrev FactorSlots (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :=
  (e : Edge) × (a : Factor) × ProgramSlot (coordinateProgram f e a P G S hG hS)
abbrev BeforeSlots (f P G S : ℕ) :=
  (c : Child) × ProgramSlot (scalarBefore f P G S c)
abbrev AfterSlots (f P G S : ℕ) (hS : 0<S) :=
  (c : Child) × ProgramSlot (scalarAfter f P G S c hS)
abbrev AddressSlot (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :=
  FactorSlots f P G S hG hS ⊕ BeforeSlots f P G S ⊕ AfterSlots f P G S hS

theorem factor_slot_bound (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :
    Fintype.card (FactorSlots f P G S hG hS)≤allCoordinateConstant := by
  change Fintype.card ((e : Edge) × (a : Factor) × ProgramSlot (coordinateProgram f e a P G S hG hS))≤_
  rw [Fintype.card_sigma]
  apply Finset.sum_le_sum
  intro e _
  rw [Fintype.card_sigma]
  apply Finset.sum_le_sum
  intro a _
  exact (program_slot_bound _).trans (coordinateProgram_constant f e a P G S hG hS)

theorem before_slot_bound (f P G S : ℕ) :
    Fintype.card (BeforeSlots f P G S)≤10*Parameters.S := by
  change Fintype.card ((c : Child) × ProgramSlot (scalarBefore f P G S c))≤_
  rw [Fintype.card_sigma]
  have h := Finset.sum_le_sum (fun (c : Child) (_ : c∈Finset.univ) =>
    (program_slot_bound (scalarBefore f P G S c)).trans_eq (scalarBefore_constant f P G S c))
  simpa only [Finset.sum_const,Finset.card_univ,child_count,smul_eq_mul,Nat.mul_comm] using h

theorem after_slot_bound (f P G S : ℕ) (hS : 0<S) :
    Fintype.card (AfterSlots f P G S hS)≤20*Parameters.S := by
  change Fintype.card ((c : Child) × ProgramSlot (scalarAfter f P G S c hS))≤_
  rw [Fintype.card_sigma]
  have h := Finset.sum_le_sum (fun (c : Child) (_ : c∈Finset.univ) =>
    (program_slot_bound (scalarAfter f P G S c hS)).trans_eq (scalarAfter_constant f P G S c hS))
  simpa only [Finset.sum_const,Finset.card_univ,child_count,smul_eq_mul,Nat.mul_comm] using h

theorem address_slot_bound (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :
    Fintype.card (AddressSlot f P G S hG hS)≤addressLocalConstant := by
  have hf := factor_slot_bound f P G S hG hS
  have hb := before_slot_bound f P G S
  have ha := after_slot_bound f P G S hS
  simp only [AddressSlot,Fintype.card_sum,addressLocalConstant]
  omega

/-- The full finite family of edge address programs has a uniform number of
file slots, independent of field width and every spectator dimension. -/
def addressSlotIndex (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :
    AddressSlot f P G S hG hS↪Fin addressLocalConstant where
  toFun slot := ((Fintype.equivFin _) slot).castLE (address_slot_bound f P G S hG hS)
  inj' x y h := by
    apply (Fintype.equivFin _).injective
    apply Fin.ext
    simpa only [Fin.coe_castLE] using congrArg (@Fin.val addressLocalConstant) h

end
end CSL.ProgramWorkspace
end ProgramWorkspace


