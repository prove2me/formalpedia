-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Memory_BaseExchangeProgram
-- name    : CSL_Interchange_Framework_Memory_BaseExchangeProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:08:57.152799+00:00
-- url     : https://prove2.me/theorems/1d3715d4-6a9b-410c-a295-0ba4e073448d
-- title:
--   Coded sorting library: Interchange / Framework / Memory / BaseExchangeProgram
-- statement:
--   Module `CodedSorting.Interchange.Framework.Memory.BaseExchangeProgram` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # An actual small-file permutation leaf
--
--   The load loop pops a real block reader into a single RAM array. Once the
--   whole file is resident, the emit loop reads that array at inverse-permuted
--   indices and pushes a real block writer. The input reader is released before
--   emission. No second payload array and no on-disk address tags are used.
--
--   `Value` is one payload unit, so V, B and the RAM bound must use the same unit.
--   The state bounds are V+B; V+2B also covers a conservative transition buffer.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Memory.BaseExchangeProgram

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Fields_BinaryPaddingScan

section InMemoryPermutation
/-!
# An actual small-file permutation leaf

The load loop pops a real block reader into a single RAM array. Once the
whole file is resident, the emit loop reads that array at inverse-permuted
indices and pushes a real block writer. The input reader is released before
emission. No second payload array and no on-disk address tags are used.

`Value` is one payload unit, so V, B and the RAM bound must use the same unit.
The state bounds are V+B; V+2B also covers a conservative transition buffer.
-/

set_option autoImplicit false

namespace CSL.InMemoryPermutation

open BucketMachine BucketReader TagErasure

variable {Value : Type*} {V : ℕ}

/-- Append to the resident array after each actual source-reader pop. -/
def load : ℕ → Reader Value → List Value → Option (Reader Value × List Value)
  | 0, reader, ram => some (reader,ram)
  | n+1, reader, ram => do
      let (value,next) ← reader.pop
      load n next (ram ++ [value])

/-- Arbitrary prefixes preserve reader validity and account for every refill. -/
theorem load_prefix (B : ℕ) (front back : List Value) (reader : Reader Value)
    (ram : List Value) (hr : reader.Valid B) (hc : reader.contents = front ++ back) :
    ∃ finalReader finalRAM,
      load front.length reader ram = some (finalReader,finalRAM) ∧
      finalReader.Valid B ∧ finalReader.contents = back ∧ finalRAM = ram ++ front ∧
      finalReader.reads+finalReader.disk.length = reader.reads+reader.disk.length := by
  induction front generalizing reader ram with
  | nil => exact ⟨reader,ram,rfl,hr,by simpa using hc,by simp,rfl⟩
  | cons a rest ih =>
    have hc' : reader.contents = a :: (rest ++ back) := by simpa using hc
    obtain ⟨next,hpop⟩ := Reader.pop_exists B reader hr a _ hc'
    have hn := Reader.pop_valid B reader next a hr hpop
    have hnc : next.contents = rest ++ back := by
      have h := Reader.pop_contents reader next a hpop
      rw [hc'] at h
      exact (List.cons.inj h).2.symm
    obtain ⟨finalReader,finalRAM,hload,hvalid,hrest,hram,hreads⟩ :=
      ih next (ram ++ [a]) hn hnc
    refine ⟨finalReader,finalRAM,?_,hvalid,hrest,?_,?_⟩
    · simpa [load,hpop] using hload
    · simpa [List.append_assoc] using hram
    · exact hreads.trans (Reader.pop_conservation reader next a hpop)

/-- All actual load prefixes keep one resident array and one reader buffer. -/
theorem load_memory (B n : ℕ) (reader finalReader : Reader Value)
    (ram finalRAM : List Value) (hr : reader.Valid B)
    (hload : load n reader ram = some (finalReader,finalRAM)) :
    finalRAM.length = ram.length+n ∧ finalReader.Valid B ∧
      finalRAM.length+finalReader.pending.length ≤ ram.length+n+B := by
  induction n generalizing reader ram with
  | zero =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hload)
    exact ⟨by omega,hr,by have h := hr.2; omega⟩
  | succ n ih =>
    cases hp : reader.pop with
    | none => simp [load,hp] at hload
    | some pair =>
      obtain ⟨a,next⟩ := pair
      have hn := Reader.pop_valid B reader next a hr hp
      have hrec : load n next (ram ++ [a]) = some (finalReader,finalRAM) := by
        simpa [load,hp] using hload
      obtain ⟨hl,hv,hm⟩ := ih next (ram++[a]) hn hrec
      simp only [List.length_append,List.length_singleton] at hl hm
      exact ⟨by omega,hv,by omega⟩

/-- Indexed RAM reads feed the output writer immediately. No output list is
materialized in RAM. The two natural-number loop counters are public control. -/
def emit (B : ℕ) (lookup : Fin V → Value) :
    (n offset : ℕ) → offset+n ≤ V → Writer Value → Writer Value
  | 0, _, _, writer => writer
  | n+1, offset, bound, writer =>
      emit B lookup n (offset+1) (by omega)
        (writer.push B (lookup ⟨offset,by omega⟩))

theorem emit_valid (B : ℕ) (lookup : Fin V → Value)
    (n offset : ℕ) (bound : offset+n ≤ V) (writer : Writer Value)
    (hw : writer.Valid B) : (emit B lookup n offset bound writer).Valid B := by
  induction n generalizing offset writer with
  | zero => exact hw
  | succ n ih => exact ih (offset+1) _ _ (Writer.push_valid B _ _ hw)

theorem emit_contents (B : ℕ) (lookup : Fin V → Value)
    (n offset : ℕ) (bound : offset+n ≤ V) (writer : Writer Value) :
    (emit B lookup n offset bound writer).contents = writer.contents ++
      List.ofFn (fun i : Fin n => lookup ⟨offset+i.val,by omega⟩) := by
  induction n generalizing offset writer with
  | zero => simp [emit]
  | succ n ih =>
    rw [emit,ih,Writer.push_contents,List.ofFn_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,List.append_assoc,List.singleton_append]
    congr 2
    apply congrArg List.ofFn
    funext i
    exact congrArg lookup (Fin.ext (by simp only [Fin.val_mk]; omega))

/-- Each emission prefix uses the original V-cell RAM array and one writer
buffer. Finished blocks are external storage. -/
theorem emit_memory (B : ℕ) (lookup : Fin V → Value)
    (n offset : ℕ) (bound : offset+n ≤ V) (writer : Writer Value)
    (hw : writer.Valid B) :
    V+(emit B lookup n offset bound writer).pending.length ≤ V+B := by
  have h := (emit_valid B lookup n offset bound writer hw).2
  omega

structure Result (Value : Type*) where
  sourceReads : ℕ
  output : Writer Value

def Result.transfers (r : Result Value) := r.sourceReads+r.output.finish.length

/-- Runtime lookup refers only to the resident array, never to a specification
function or an independently supplied target file. -/
def run (e : Equiv.Perm (Fin V)) (B : ℕ) (sourceBlocks : List (List Value)) :
    Option (Result Value) := do
  let (reader,ram) ← load V (Reader.fromDisk sourceBlocks) []
  if hram : ram.length = V then
    let lookup := fun i : Fin V => ram.get ⟨(e.symm i).val,by omega⟩
    return ⟨reader.reads,emit B lookup V 0 (by omega) Writer.empty⟩
  else none

private theorem get_input (F : Fin V → Value) (i : Fin V) (h : i.val < (inputValues F).length) :
    (inputValues F).get ⟨i.val,h⟩ = F i := by
  simp [inputValues]

/-- One actual read scan, arbitrary free internal computation on the resident
array, and one actual write scan. Output blocking is canonical. -/
theorem run_correct (e : Equiv.Perm (Fin V)) (F : Fin V → Value)
    (B : ℕ) (hB : 0 < B) :
    ∃ result,
      run e B (pack B hB (inputValues F)) = some result ∧
      result.output.finish = pack B hB (outputValues e F) ∧
      result.output.Valid B ∧ result.transfers = 2*((V+B-1)/B) := by
  let file := pack B hB (inputValues F)
  have hin : (inputValues F).length = V := by simp [inputValues]
  have hreader := StreamCopy.pack_reader_valid B hB (inputValues F)
  have hc : (Reader.fromDisk file).contents = inputValues F ++ [] := by
    simp [file,Reader.contents,Reader.fromDisk,flatten_pack]
  obtain ⟨reader,ram,hl,hr,hcontents,hram,hreads⟩ :=
    load_prefix B (inputValues F) [] (Reader.fromDisk file) [] hreader hc
  have hram' : ram = inputValues F := by simpa using hram
  subst ram
  simp only [List.nil_append,hin] at hl
  try dsimp only [file] at hl
  have hdisk := Reader.empty_contents_disk B reader hr hcontents
  have hcount : reader.reads = (V+B-1)/B := by
    simpa [hdisk,Reader.fromDisk,file,pack_count,hin] using hreads
  let lookup : Fin V → Value := fun i => (inputValues F).get ⟨(e.symm i).val,by omega⟩
  have hlookup : lookup = fun i => F (e.symm i) := by
    funext i
    exact get_input F (e.symm i) _
  let writer := emit B lookup V 0 (by omega) Writer.empty
  have hw : writer.Valid B := emit_valid B lookup V 0 (by omega) _ (Writer.empty_valid B hB)
  have hout : writer.contents = outputValues e F := by
    rw [emit_contents]
    simp only [Writer.contents,Writer.empty,List.flatten_nil,List.nil_append,Nat.zero_add]
    rw [hlookup]
    simp [outputValues,List.ofFn_eq_map]
  refine ⟨⟨reader.reads,writer⟩,?_,?_,hw,?_⟩
  · unfold run
    rw [hl]
    try dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd]
    rw [dif_pos hin]
    rfl
  · rw [DiskStreamPass.writer_finish_eq_pack B hB writer hw,hout]
  · change reader.reads+writer.finish.length = _
    rw [hcount,Writer.finish_count B writer hw,hout]
    simp [outputValues]
    omega

/-- Multiplying by the block size retains the partial-block startup. -/
theorem run_scaled (e : Equiv.Perm (Fin V)) (F : Fin V → Value)
    (B : ℕ) (hB : 0 < B) :
    ∃ result,
      run e B (pack B hB (inputValues F)) = some result ∧
      result.output.finish = pack B hB (outputValues e F) ∧
      result.output.Valid B ∧ result.transfers*B ≤ 2*(V+B) := by
  obtain ⟨r,hrun,hout,hvalid,hcost⟩ := run_correct e F B hB
  refine ⟨r,hrun,hout,hvalid,?_⟩
  rw [hcost]
  have h := (Nat.div_mul_le_self (V+B-1) B).trans (Nat.sub_le (V+B) 1)
  nlinarith

/-- Specialize the load invariant to every prefix of a file fitting in RAM. -/
theorem file_load_memory (B n : ℕ) (hn : n ≤ V)
    (reader finalReader : Reader Value) (finalRAM : List Value)
    (hr : reader.Valid B)
    (hload : load n reader [] = some (finalReader,finalRAM)) :
    finalRAM.length+finalReader.pending.length ≤ V+B := by
  have h := (load_memory B n reader finalReader [] finalRAM hr hload).2.2
  simp only [List.length_nil,Nat.zero_add] at h
  omega

/-- A conservative leaf RAM condition, in the same units as the block size. -/
theorem leaf_memory_fits (M B : ℕ) (hfit : V+2*B ≤ M) : V+B ≤ M := by omega

end CSL.InMemoryPermutation
end InMemoryPermutation

section BaseExchangeProgram
/-!
# Buffered leaf exchange

One global distribution uses the ordered pair of exchanged field values as
its bucket index. Within each bucket the unchanged prefix, gap and suffix
retain their original order. The resulting disk-to-disk pass has Q² buffers,
not one new set of buffers per prefix. Every runtime read and write comes
from `DiskStreamPass`; bucket files contain payloads only.

All volume, block and resident-memory counts below use the same payload
unit. For bit streams the block parameter is the number of bits per physical
block. The Q² startup term is explicit and requires a separate parameter
argument before it can be absorbed into a scan bound.
-/

set_option autoImplicit false

namespace CSL.BaseExchangeProgram

open Address CoordinateScans ScanProgram BucketMachine TagErasure

variable {P Q G S : ℕ}

abbrev Volume (P Q G S : ℕ) := (P * (Q * G)) * (Q * S)

/-- The physical layout is the original prefix/high/gap/low/suffix order. -/
def permutation : Equiv.Perm (Fin (Volume P Q G S)) :=
  lowLayout.symm.trans (exchangeEquiv.trans lowLayout)

/-- There are exactly Q² bucket identifiers, shared by all spectators. -/
def key (x : Fin (Volume P Q G S)) : Fin (Q * Q) :=
  finProdFinEquiv ((lowLayout.symm x).high, (lowLayout.symm x).low)

@[simp] theorem permutation_encoded
    (a : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)) :
    permutation (lowLayout a) = lowLayout (exchange a) := by
  simp [permutation, exchangeEquiv]

@[simp] theorem key_encoded
    (a : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)) :
    key (lowLayout a) = finProdFinEquiv (a.high, a.low) := by
  simp [key]

private theorem exchange_balance
    (a : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)) :
    (lowLayout (exchange a)).val + (S*a.low.val + (Q*S)*G*a.high.val) =
      (lowLayout a).val + (S*a.high.val + (Q*S)*G*a.low.val) := by
  simp only [lowLayout_val, exchange]
  ring

/-- In one bucket, exchanging the two fixed fields preserves address order. -/
theorem increasing_streams (x y : Fin (Volume P Q G S))
    (hxy : x < y) (hkey : key x = key y) : permutation x < permutation y := by
  let a := lowLayout.symm x
  let b := lowLayout.symm y
  have hp : (a.high,a.low) = (b.high,b.low) := finProdFinEquiv.injective hkey
  have hh : a.high = b.high := congrArg (fun z : Fin Q × Fin Q => z.1) hp
  have hd : a.low = b.low := congrArg (fun z : Fin Q × Fin Q => z.2) hp
  have ha := exchange_balance a
  have hb := exchange_balance b
  have hx : lowLayout a = x := lowLayout.apply_symm_apply x
  have hy : lowLayout b = y := lowLayout.apply_symm_apply y
  have hpx : lowLayout (exchange a) = permutation x := by rw [← hx,permutation_encoded]
  have hpy : lowLayout (exchange b) = permutation y := by rw [← hy,permutation_encoded]
  rw [hx,hpx,hh,hd] at ha
  rw [hy,hpy] at hb
  change x.val < y.val at hxy
  change (permutation x).val < (permutation y).val
  omega

/-- The executable program consists of one actual buffered distribution pass. -/
def program : List (Pass (Volume P Q G S)) :=
  [.streams (Q*Q) permutation key increasing_streams]

@[simp] theorem destination_program :
    destination (program (P := P) (Q := Q) (G := G) (S := S)) = permutation := rfl

@[simp] theorem constant_program :
    totalConstant (program (P := P) (Q := Q) (G := G) (S := S)) = 2*(Q*Q)+6 := rfl

/-- Functional exchange of the entire fields, with every spectator untouched. -/
theorem eval_encoded {Value : Type*} (F : Fin (Volume P Q G S) → Value)
    (a : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)) :
    eval program F (lowLayout a) = F (lowLayout (exchange a)) := by
  rw [eval_eq_pullback,destination_program]
  simp [permutation, exchangeEquiv]

/-- Canonically blocked output is produced by source-reader and bucket-reader
loops feeding actual writers; no additional uncharged repacking is used. -/
theorem disk_execution {Value : Type*}
    (F : Fin (Volume P Q G S) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ result : DiskStreamPass.PassResult (Q*Q) Value,
      DiskStreamPass.run (permutation (P := P) (Q := Q) (G := G) (S := S))
        (key (P := P) (Q := Q) (G := G) (S := S)) B (pack B hB (inputValues F)) = some result ∧
      result.output.finish = pack B hB (outputValues permutation F) ∧
      result.transfers ≤ 4*(Volume P Q G S/B)+2*(Q*Q)+2 ∧
      result.output.Valid B ∧ (∀ k, (result.readers k).Valid B) :=
  DiskStreamPass.run_packed_canonical permutation key increasing_streams F B hB

/-- The same physical run is a `ScanProgram.Execution`, retaining its sharper
Q²-startup charge rather than multiplying that charge by the volume. -/
theorem execution {Value : Type*} [Inhabited Value]
    (F : Fin (Volume P Q G S) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ cost, Execution B hB program F cost ∧
      cost ≤ 4*(Volume P Q G S/B)+2*(Q*Q)+2 := by
  obtain ⟨r,hrun,hout,hcost,hw,hr⟩ := disk_execution F B hB
  refine ⟨r.transfers,?_,hcost⟩
  have he : StepEvidence (.streams (Q*Q) permutation key increasing_streams) F B hB
      r.transfers := ⟨r,hrun,hout,rfl,hw,hr⟩
  have h := Execution.cons (.streams (Q*Q) permutation key increasing_streams) [] F
    r.transfers 0 he (Execution.nil _)
  first
  | exact h
  | (have h_sx := h; simp only [Nat.add_zero] at h_sx ⊢; exact h_sx)
  | (have h_sx := h; simp only [Nat.add_zero] at h_sx; exact h_sx)
  | (simp only [Nat.add_zero]; exact h)

/-- Startup is absorbed only under an explicit volume/buffer relation. -/
theorem execution_scaled {Value : Type*} [Inhabited Value]
    (F : Fin (Volume P Q G S) → Value) (B : ℕ) (hB : 0 < B)
    (hstartup : (Q*Q)*B ≤ Volume P Q G S+B) :
    ∃ cost, Execution B hB program F cost ∧
      cost*B ≤ 6*(Volume P Q G S+B) := by
  obtain ⟨cost,hexec,hcost⟩ := execution F B hB
  refine ⟨cost,hexec,?_⟩
  have hscaled := Nat.mul_le_mul_right B hcost
  have hdiv : (Volume P Q G S/B)*B ≤ Volume P Q G S := Nat.div_mul_le_self _ _
  nlinarith

/-- An early-cutoff leaf uses the same exchange permutation but loads the
whole small file into RAM; its buffer count does not grow with Q². -/
theorem in_memory_execution {Value : Type*}
    (F : Fin (Volume P Q G S) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ result,
      InMemoryPermutation.run (permutation (P := P) (Q := Q) (G := G) (S := S)) B
        (pack B hB (inputValues F)) = some result ∧
      result.output.finish = pack B hB (outputValues permutation F) ∧
      result.output.Valid B ∧ result.transfers*B ≤ 2*(Volume P Q G S+B) :=
  InMemoryPermutation.run_scaled permutation F B hB

/-- This bounds every reader/writer prefix of the distribution phase. -/
theorem distribution_memory {Value : Type*} (B : ℕ)
    (n offset : ℕ) (bound : offset+n ≤ Volume P Q G S)
    (source finalSource : BucketReader.Reader Value)
    (buckets finalBuckets : Fin (Q*Q) → Writer Value)
    (hs : source.Valid B) (hb : ∀ k, (buckets k).Valid B)
    (hdone : DiskStreamPass.distribute key B n offset bound source buckets =
      some (finalSource,finalBuckets)) :
    finalSource.pending.length + writerOccupancy finalBuckets ≤ (Q*Q+2)*B :=
  DiskStreamPass.distribute_prefix_memory key B n offset bound source finalSource
    buckets finalBuckets hs hb hdone

/-- This also bounds every prefix of the reconstruction phase. -/
theorem reconstruction_memory {Value : Type*} (B : ℕ)
    (n offset : ℕ) (bound : offset+n ≤ Volume P Q G S)
    (readers finalReaders : Fin (Q*Q) → BucketReader.Reader Value)
    (writer finalWriter : Writer Value)
    (hr : ∀ k, (readers k).Valid B) (hw : writer.Valid B)
    (hdone : DiskStreamPass.reconstruct (fun y => key (permutation.symm y)) B n offset bound
      readers writer = some (finalReaders,finalWriter)) :
    BucketReader.occupiedReaders finalReaders + finalWriter.pending.length ≤ (Q*Q+2)*B :=
  DiskStreamPass.reconstruct_prefix_memory (fun y => key (permutation.symm y)) B n offset
    bound readers finalReaders writer finalWriter hr hw hdone

theorem buffers (p : Pass (Volume P Q G S)) (hp : p ∈ program) : p.buffers = Q*Q+2 := by
  simp only [program,List.mem_singleton] at hp
  subst p
  rfl

/-- Radix-q fields of width e use q^(2e) buckets. -/
theorem radix_bucket_count (q e : ℕ) : (q^e)*(q^e) = q^(2*e) := by
  rw [← pow_add]
  congr 1
  omega

/-- A separate admissibility premise expresses that the bucket buffers fit. -/
theorem memory_fits (M B : ℕ) (hfit : (Q*Q+2)*B ≤ M)
    (p : Pass (Volume P Q G S)) (hp : p ∈ program) : p.buffers*B ≤ M := by
  rw [buffers p hp]
  exact hfit

/-- Both leaf implementations return a physical file and actual transfer count. -/
structure LeafResult (Value : Type*) where
  output : Writer Value
  transfers : ℕ

/-- The public volume test selects RAM for a small file, otherwise Q² streams. -/
def adaptiveRun {Value : Type*} (cutoff B : ℕ) (source : List (List Value)) :
    Option (LeafResult Value) :=
  if Volume P Q G S ≤ cutoff then
    (InMemoryPermutation.run (permutation (P := P) (Q := Q) (G := G) (S := S)) B source).map
      (fun r => ⟨r.output,r.transfers⟩)
  else
    (DiskStreamPass.run (permutation (P := P) (Q := Q) (G := G) (S := S))
      (key (P := P) (Q := Q) (G := G) (S := S)) B source).map
      (fun r => ⟨r.output,r.transfers⟩)

/-- One interface supplies both early-stop RAM leaves and width-zero bucket
leaves. The startup premise is needed only when the RAM branch is not taken. -/
theorem adaptive_correct {Value : Type*}
    (F : Fin (Volume P Q G S) → Value) (cutoff B : ℕ) (hB : 0 < B)
    (hstartup : cutoff < Volume P Q G S → (Q*Q)*B ≤ Volume P Q G S+B) :
    ∃ result,
      adaptiveRun (P := P) (Q := Q) (G := G) (S := S) cutoff B
        (pack B hB (inputValues F)) = some result ∧
      result.output.finish = pack B hB (outputValues permutation F) ∧
      result.output.Valid B ∧ result.transfers*B ≤ 6*(Volume P Q G S+B) := by
  by_cases hs : Volume P Q G S ≤ cutoff
  · obtain ⟨r,hrun,hout,hvalid,hcost⟩ := in_memory_execution F B hB
    refine ⟨⟨r.output,r.transfers⟩,?_,hout,hvalid,?_⟩
    · simp only [adaptiveRun,hs,↓reduceIte,hrun,Option.map_some]
      try rfl
    · change r.transfers*B ≤ _
      try omega
  · obtain ⟨r,hrun,hout,hcost,hvalid,hreaders⟩ := disk_execution F B hB
    refine ⟨⟨r.output,r.transfers⟩,?_,hout,hvalid,?_⟩
    · simp only [adaptiveRun,hs,↓reduceIte,hrun,Option.map_some]
      try rfl
    · change r.transfers*B ≤ _
      have hscaled := Nat.mul_le_mul_right B hcost
      have hdiv : (Volume P Q G S/B)*B ≤ Volume P Q G S := Nat.div_mul_le_self _ _
      have hb := hstartup (by omega)
      nlinarith

def adaptiveResident (cutoff B : ℕ) : ℕ :=
  if Volume P Q G S ≤ cutoff then Volume P Q G S+2*B else (Q*Q+2)*B

/-- The small-file cutoff reserves two blocks. In the other branch only the
Q² bucket buffers and two streaming buffers are resident. -/
theorem adaptive_memory_fits (cutoff B M : ℕ)
    (hram : cutoff+2*B ≤ M)
    (hbucket : cutoff < Volume P Q G S → (Q*Q+2)*B ≤ M) :
    adaptiveResident (P := P) (Q := Q) (G := G) (S := S) cutoff B ≤ M := by
  unfold adaptiveResident
  split_ifs with h
  · omega
  · exact hbucket (by omega)

end CSL.BaseExchangeProgram
end BaseExchangeProgram


