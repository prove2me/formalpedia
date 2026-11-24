-- Prove2me | Definitions.Def_CSL_Sorting_Bounds_MergeRounds
-- name    : CSL_Sorting_Bounds_MergeRounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:56:03.426914+00:00
-- url     : https://prove2.me/theorems/7fe2eaf1-9ba3-4920-8500-18aadbfa361b
-- title:
--   Coded sorting library: Sorting / Bounds / MergeRounds
-- statement:
--   Module `CodedSorting.Sorting.Bounds.MergeRounds` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   A genuine buffered two-way merge: two input blocks, one output block,
--   and two retained head records. Only refills and writer flushes count as I/O.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.Bounds.MergeRounds

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Memory_StreamCopy
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Log

section ExternalMerge
/-! A genuine buffered two-way merge: two input blocks, one output block,
and two retained head records. Only refills and writer flushes count as I/O. -/
namespace CSL.ExternalMerge
open BucketMachine BucketReader StreamCopy
variable {α : Type*}

/-- One retained comparison key and the unread tail of its buffered stream. -/
structure Cursor (α : Type*) where
  head : Option α
  reader : Reader α

def Cursor.contents (c : Cursor α) := c.head.toList ++ c.reader.contents

def Cursor.Valid (B : ℕ) (c : Cursor α) :=
  c.reader.Valid B ∧ (c.head = none → c.reader.contents = [])

def Cursor.load (reader : Reader α) : Cursor α :=
  match reader.pop with
  | none => ⟨none,reader⟩
  | some (a,next) => ⟨some a,next⟩

theorem pop_none_iff (B : ℕ) (reader : Reader α) (hr : reader.Valid B) :
    reader.pop = none ↔ reader.contents = [] := by
  constructor
  · intro hp
    cases hc : reader.contents with
    | nil => rfl
    | cons a rest =>
      obtain ⟨next,he⟩ := Reader.pop_exists B reader hr a rest hc
      rw [hp] at he
      contradiction
  · intro hc
    cases hp : reader.pop with
    | none => rfl
    | some pair =>
      have he := Reader.pop_contents reader pair.2 pair.1 hp
      rw [hc] at he
      contradiction

theorem Cursor.load_spec (B : ℕ) (reader : Reader α) (hr : reader.Valid B) :
    (load reader).Valid B ∧ (load reader).contents = reader.contents ∧
      (load reader).reader.reads+(load reader).reader.disk.length =
        reader.reads+reader.disk.length := by
  unfold load
  cases hp : reader.pop with
  | none =>
    have he := (pop_none_iff B reader hr).1 hp
    exact ⟨⟨hr,fun _ => he⟩,by simp [Cursor.contents],rfl⟩
  | some pair =>
    rcases pair with ⟨a,next⟩
    have hv := Reader.pop_valid B reader next a hr hp
    have hc := Reader.pop_contents reader next a hp
    exact ⟨⟨hv,by simp⟩,by simpa [Cursor.contents] using hc.symm,
      Reader.pop_conservation reader next a hp⟩

theorem Cursor.none_of_contents_nil (c : Cursor α) (hc : c.contents = []) : c.head = none := by
  cases h : c.head with
  | none => rfl
  | some a => simp [Cursor.contents,h] at hc

theorem Cursor.head_tail (B : ℕ) (c : Cursor α) (hv : c.Valid B)
    (a : α) (tail : List α) (hc : c.contents = a::tail) :
    c.head = some a ∧ c.reader.contents = tail := by
  cases he : c.head with
  | none =>
    have hn := hv.2 he
    simp [Cursor.contents,he,hn] at hc
  | some b =>
    simp only [Cursor.contents,he,Option.toList_some,List.cons_append,List.nil_append,
      List.cons.injEq] at hc
    exact ⟨congrArg some hc.1,hc.2⟩

structure State (α : Type*) where
  left : Cursor α
  right : Cursor α
  writer : Writer α

def State.Valid (B : ℕ) (s : State α) := s.left.Valid B ∧ s.right.Valid B ∧ s.writer.Valid B

def State.memory (s : State α) :=
  s.left.reader.pending.length+s.right.reader.pending.length+s.writer.pending.length+
    s.left.head.toList.length+s.right.head.toList.length

def emitLeft (B : ℕ) (a : α) (s : State α) : State α :=
  ⟨Cursor.load s.left.reader,s.right,s.writer.push B a⟩

def emitRight (B : ℕ) (a : α) (s : State α) : State α :=
  ⟨s.left,Cursor.load s.right.reader,s.writer.push B a⟩

def step (B : ℕ) (le : α → α → Bool) (s : State α) : Option (State α) :=
  match s.left.head,s.right.head with
  | none,none => none
  | some a,none => some (emitLeft B a s)
  | none,some b => some (emitRight B b s)
  | some a,some b => if le a b then some (emitLeft B a s) else some (emitRight B b s)

def run (B : ℕ) (le : α → α → Bool) : ℕ → State α → State α
  | 0,s => s
  | fuel+1,s => match step B le s with
    | none => s
    | some next => run B le fuel next

/-- This invariant holds at every intermediate state, including refills. -/
theorem valid_memory (B : ℕ) (s : State α) (hv : s.Valid B) : s.memory ≤ 3*B+2 := by
  have hl := hv.1.1.2
  have hr := hv.2.1.1.2
  have hw := hv.2.2.2
  have hhl : s.left.head.toList.length ≤ 1 := by cases s.left.head <;> simp
  have hhr : s.right.head.toList.length ≤ 1 := by cases s.right.head <;> simp
  unfold State.memory
  omega

theorem emitLeft_valid (B : ℕ) (a : α) (s : State α) (hv : s.Valid B) :
    (emitLeft B a s).Valid B :=
  ⟨(Cursor.load_spec B s.left.reader hv.1.1).1,hv.2.1,
    Writer.push_valid B s.writer a hv.2.2⟩

theorem emitRight_valid (B : ℕ) (a : α) (s : State α) (hv : s.Valid B) :
    (emitRight B a s).Valid B :=
  ⟨hv.1,(Cursor.load_spec B s.right.reader hv.2.1.1).1,
    Writer.push_valid B s.writer a hv.2.2⟩

/-- Both input conservation equations count actual refills, independently. -/
def Conserved (s t : State α) :=
  t.left.reader.reads+t.left.reader.disk.length = s.left.reader.reads+s.left.reader.disk.length ∧
  t.right.reader.reads+t.right.reader.disk.length = s.right.reader.reads+s.right.reader.disk.length

theorem Conserved.trans {s t u : State α} (h : Conserved s t) (h' : Conserved t u) :
    Conserved s u := ⟨h'.1.trans h.1,h'.2.trans h.2⟩

theorem emitLeft_conserved (B : ℕ) (a : α) (s : State α) (hv : s.Valid B) :
    Conserved s (emitLeft B a s) :=
  ⟨(Cursor.load_spec B s.left.reader hv.1.1).2.2,rfl⟩

theorem emitRight_conserved (B : ℕ) (a : α) (s : State α) (hv : s.Valid B) :
    Conserved s (emitRight B a s) :=
  ⟨rfl,(Cursor.load_spec B s.right.reader hv.2.1.1).2.2⟩

/-- Actual execution agrees with List.merge on every input, without
assuming the lists were sorted. Sortedness is applied only afterward. -/
theorem run_correct (B : ℕ) (le : α → α → Bool) (xs ys : List α)
    (s : State α) (hv : s.Valid B) (hl : s.left.contents = xs) (hr : s.right.contents = ys) :
    let t := run B le (xs.length+ys.length) s
    t.Valid B ∧ t.left.contents=[] ∧ t.right.contents=[] ∧
      t.writer.contents=s.writer.contents++List.merge xs ys le ∧ Conserved s t := by
  induction xs generalizing ys s with
  | nil =>
    induction ys generalizing s with
    | nil => exact ⟨hv,hl,hr,by simp [run],⟨rfl,rfl⟩⟩
    | cons b ys ih =>
      have hln := Cursor.none_of_contents_nil s.left hl
      obtain ⟨hrh,hrt⟩ := Cursor.head_tail B s.right hv.2.1 b ys hr
      have hs : step B le s = some (emitRight B b s) := by simp [step,hln,hrh]
      have hnext : (emitRight B b s).right.contents=ys :=
        (Cursor.load_spec B s.right.reader hv.2.1.1).2.1.trans hrt
      have h := ih (emitRight B b s) (emitRight_valid B b s hv) hl hnext
      try dsimp only at h
      simp only [List.length_nil,Nat.zero_add,Nat.add_zero] at h
      have he : run B le (([] : List α).length+(b::ys).length) s = run B le ys.length (emitRight B b s) := by
        simp [run,hs]
      rw [he]
      refine ⟨h.1,h.2.1,h.2.2.1,?_,(emitRight_conserved B b s hv).trans h.2.2.2.2⟩
      rw [h.2.2.2.1]
      simp [emitRight,Writer.push_contents,List.append_assoc]
  | cons a xs ih =>
    induction ys generalizing s with
    | nil =>
      obtain ⟨hlh,hlt⟩ := Cursor.head_tail B s.left hv.1 a xs hl
      have hrn := Cursor.none_of_contents_nil s.right hr
      have hs : step B le s = some (emitLeft B a s) := by simp [step,hlh,hrn]
      have hnext : (emitLeft B a s).left.contents=xs :=
        (Cursor.load_spec B s.left.reader hv.1.1).2.1.trans hlt
      have h := ih [] (emitLeft B a s) (emitLeft_valid B a s hv) hnext hr
      try dsimp only at h
      simp only [List.length_nil,Nat.zero_add,Nat.add_zero] at h
      have he : run B le ((a::xs).length+([] : List α).length) s = run B le xs.length (emitLeft B a s) := by
        simp [run,hs]
      rw [he]
      refine ⟨h.1,h.2.1,h.2.2.1,?_,(emitLeft_conserved B a s hv).trans h.2.2.2.2⟩
      rw [h.2.2.2.1]
      simp [emitLeft,Writer.push_contents,List.append_assoc]
    | cons b ys ihy =>
      obtain ⟨hlh,hlt⟩ := Cursor.head_tail B s.left hv.1 a xs hl
      obtain ⟨hrh,hrt⟩ := Cursor.head_tail B s.right hv.2.1 b ys hr
      by_cases hab : le a b = true
      · have hs : step B le s = some (emitLeft B a s) := by simp [step,hlh,hrh,hab]
        have hnext : (emitLeft B a s).left.contents=xs :=
          (Cursor.load_spec B s.left.reader hv.1.1).2.1.trans hlt
        have h := ih (b::ys) (emitLeft B a s) (emitLeft_valid B a s hv) hnext hr
        try dsimp only at h
        have he : run B le ((a::xs).length+(b::ys).length) s =
            run B le (xs.length+(b::ys).length) (emitLeft B a s) := by
          simp only [List.length_cons]
          rw [show xs.length+1+(ys.length+1)=(xs.length+(ys.length+1))+1 by omega,run,hs]
        rw [he]
        refine ⟨h.1,h.2.1,h.2.2.1,?_,(emitLeft_conserved B a s hv).trans h.2.2.2.2⟩
        rw [h.2.2.2.1]
        simp [List.merge,hab,emitLeft,Writer.push_contents,List.append_assoc]
      · have hs : step B le s = some (emitRight B b s) := by simp [step,hlh,hrh,hab]
        have hnext : (emitRight B b s).right.contents=ys :=
          (Cursor.load_spec B s.right.reader hv.2.1.1).2.1.trans hrt
        have h := ihy (emitRight B b s) (emitRight_valid B b s hv) hl hnext
        try dsimp only at h
        have he : run B le ((a::xs).length+(b::ys).length) s =
            run B le ((a::xs).length+ys.length) (emitRight B b s) := by
          simp only [List.length_cons]
          rw [show xs.length+1+(ys.length+1)=(xs.length+1+ys.length)+1 by omega,run,hs]
        rw [he]
        refine ⟨h.1,h.2.1,h.2.2.1,?_,(emitRight_conserved B b s hv).trans h.2.2.2.2⟩
        rw [h.2.2.2.1]
        simp [List.merge,hab,emitRight,Writer.push_contents,List.append_assoc]

theorem step_valid (B : ℕ) (le : α → α → Bool) (s t : State α)
    (hv : s.Valid B) (ht : step B le s=some t) : t.Valid B := by
  unfold step at ht
  cases hl : s.left.head <;> cases hr : s.right.head <;> simp only [hl,hr] at ht
  · contradiction
  · exact Option.some.inj ht ▸ emitRight_valid B _ s hv
  · exact Option.some.inj ht ▸ emitLeft_valid B _ s hv
  · split_ifs at ht
    · exact Option.some.inj ht ▸ emitLeft_valid B _ s hv
    · exact Option.some.inj ht ▸ emitRight_valid B _ s hv

theorem run_valid (B : ℕ) (le : α → α → Bool) (fuel : ℕ)
    (s : State α) (hv : s.Valid B) : (run B le fuel s).Valid B := by
  induction fuel generalizing s with
  | zero => exact hv
  | succ fuel ih =>
    cases hs : step B le s with
    | none => simpa only [run,hs] using hv
    | some next => simpa only [run,hs] using ih next (step_valid B le s next hv hs)

theorem run_memory (B : ℕ) (le : α → α → Bool) (fuel : ℕ)
    (s : State α) (hv : s.Valid B) : (run B le fuel s).memory ≤ 3*B+2 :=
  valid_memory B _ (run_valid B le fuel s hv)

def initial (left right : Reader α) : State α :=
  ⟨Cursor.load left,Cursor.load right,Writer.empty⟩

def packedRun (B : ℕ) (hB : 0 < B) (le : α → α → Bool) (xs ys : List α) : State α :=
  run B le (xs.length+ys.length)
    (initial (Reader.fromDisk (pack B hB xs)) (Reader.fromDisk (pack B hB ys)))

def transfers (s : State α) := s.left.reader.reads+s.right.reader.reads+s.writer.finish.length

/-- The actual run reads each input block exactly once and writes exactly
the packed length of the output. Refills consumed by initial head loads are
included in the counters. -/
theorem packedRun_spec (B : ℕ) (hB : 0 < B) (le : α → α → Bool) (xs ys : List α) :
    let t := packedRun B hB le xs ys
    t.Valid B ∧ t.writer.finish.flatten=List.merge xs ys le ∧
      t.left.reader.reads=(xs.length+B-1)/B ∧
      t.right.reader.reads=(ys.length+B-1)/B ∧
      t.writer.finish.length=(xs.length+ys.length+B-1)/B := by
  let left := Reader.fromDisk (pack B hB xs)
  let right := Reader.fromDisk (pack B hB ys)
  have hleft : left.Valid B := pack_reader_valid B hB xs
  have hright : right.Valid B := pack_reader_valid B hB ys
  have hl := Cursor.load_spec B left hleft
  have hr := Cursor.load_spec B right hright
  have hv : (initial left right).Valid B := ⟨hl.1,hr.1,Writer.empty_valid B hB⟩
  have hlc : (initial left right).left.contents=xs := by
    change (Cursor.load left).contents=xs
    rw [hl.2.1]
    simp [left,Reader.contents,Reader.fromDisk,flatten_pack]
  have hrc : (initial left right).right.contents=ys := by
    change (Cursor.load right).contents=ys
    rw [hr.2.1]
    simp [right,Reader.contents,Reader.fromDisk,flatten_pack]
  have h := run_correct B le xs ys (initial left right) hv hlc hrc
  let t := packedRun B hB le xs ys
  change t.Valid B ∧ t.left.contents=[] ∧ t.right.contents=[] ∧
    t.writer.contents=Writer.empty.contents++List.merge xs ys le ∧ Conserved (initial left right) t at h
  have hcontents : t.writer.contents=List.merge xs ys le := by
    simpa [Writer.contents,Writer.empty] using h.2.2.2.1
  have hlreader : t.left.reader.contents=[] := (List.append_eq_nil_iff.mp h.2.1).2
  have hrreader : t.right.reader.contents=[] := (List.append_eq_nil_iff.mp h.2.2.1).2
  have hldisk := Reader.empty_contents_disk B t.left.reader h.1.1.1 hlreader
  have hrdisk := Reader.empty_contents_disk B t.right.reader h.1.2.1.1 hrreader
  have hreadsL := h.2.2.2.2.1.trans hl.2.2
  have hreadsR := h.2.2.2.2.2.trans hr.2.2
  refine ⟨h.1,?_,?_,?_,?_⟩
  · rw [Writer.finish_contents,hcontents]
  · simpa [left,Reader.fromDisk,hldisk,pack_count] using hreadsL
  · simpa [right,Reader.fromDisk,hrdisk,pack_count] using hreadsR
  · rw [Writer.finish_count B t.writer h.1.2.2,hcontents]
    rw [(List.merge_perm_append le).length_eq,List.length_append]

/-- Exact total read/write count, before estimating it by a scan bound. -/
theorem packedRun_transfers (B : ℕ) (hB : 0 < B) (le : α → α → Bool) (xs ys : List α) :
    transfers (packedRun B hB le xs ys) =
      (xs.length+B-1)/B+(ys.length+B-1)/B+(xs.length+ys.length+B-1)/B := by
  have h := packedRun_spec B hB le xs ys
  unfold transfers
  rw [h.2.2.1,h.2.2.2.1,h.2.2.2.2]

theorem packedRun_scan_bound (B : ℕ) (hB : 0 < B) (le : α → α → Bool) (xs ys : List α) :
    transfers (packedRun B hB le xs ys)*B ≤ 2*(xs.length+ys.length)+3*B := by
  rw [packedRun_transfers]
  have hl := Nat.le_of_lt (pack_capacity B hB xs).2
  have hr := Nat.le_of_lt (pack_capacity B hB ys).2
  have ho := Nat.le_of_lt (pack_capacity B hB (xs++ys)).2
  rw [pack_count] at hl hr ho
  simp only [List.length_append] at ho
  nlinarith only [hl,hr,ho]

/-- Sorting and permutation conservation are conclusions about the output
of the buffered machine, rather than an unrelated specification merge. -/
theorem packedRun_sorted [LinearOrder α] (B : ℕ) (hB : 0 < B) (xs ys : List α)
    (hxs : xs.Pairwise (·≤·)) (hys : ys.Pairwise (·≤·)) :
    let t := packedRun B hB (fun a b => decide (a≤b)) xs ys
    t.writer.finish.flatten.Pairwise (·≤·) ∧ t.writer.finish.flatten.Perm (xs++ys) := by
  try dsimp only
  rw [(packedRun_spec B hB (fun a b => decide (a≤b)) xs ys).2.1]
  exact ⟨List.Sorted.merge hxs hys,List.merge_perm_append _⟩

end CSL.ExternalMerge
end ExternalMerge

section ExternalMergeFiles
/-! Merge existing block files directly; no free repacking is inserted
between rounds. All output files come from the writer's actual flushes. -/
namespace CSL.ExternalMergeFiles
open BucketMachine BucketReader ExternalMerge
variable {α : Type*}

def fileRun (B : ℕ) (le : α → α → Bool) (xs ys : List (List α)) : State α :=
  run B le (xs.flatten.length+ys.flatten.length)
    (initial (Reader.fromDisk xs) (Reader.fromDisk ys))

/-- The actual run reads each input block exactly once and writes exactly
the packed length of the output. Refills consumed by initial head loads are
included in the counters. -/
theorem fileRun_spec (B : ℕ) (hB : 0 < B) (le : α → α → Bool)
    (xs ys : List (List α)) (hxs : (Reader.fromDisk xs).Valid B)
    (hys : (Reader.fromDisk ys).Valid B) :
    let t := fileRun B le xs ys
    t.Valid B ∧ t.writer.finish.flatten=List.merge xs.flatten ys.flatten le ∧
      t.left.reader.reads=xs.length ∧
      t.right.reader.reads=ys.length ∧
      t.writer.finish.length=(xs.flatten.length+ys.flatten.length+B-1)/B := by
  let left := Reader.fromDisk xs
  let right := Reader.fromDisk ys
  have hleft : left.Valid B := hxs
  have hright : right.Valid B := hys
  have hl := Cursor.load_spec B left hleft
  have hr := Cursor.load_spec B right hright
  have hv : (initial left right).Valid B := ⟨hl.1,hr.1,Writer.empty_valid B hB⟩
  have hlc : (initial left right).left.contents=xs.flatten := by
    change (Cursor.load left).contents=xs.flatten
    rw [hl.2.1]
    simp [left,Reader.contents,Reader.fromDisk,flatten_pack]
  have hrc : (initial left right).right.contents=ys.flatten := by
    change (Cursor.load right).contents=ys.flatten
    rw [hr.2.1]
    simp [right,Reader.contents,Reader.fromDisk,flatten_pack]
  have h := run_correct B le xs.flatten ys.flatten (initial left right) hv hlc hrc
  let t := fileRun B le xs ys
  change t.Valid B ∧ t.left.contents=[] ∧ t.right.contents=[] ∧
    t.writer.contents=Writer.empty.contents++List.merge xs.flatten ys.flatten le ∧ Conserved (initial left right) t at h
  have hcontents : t.writer.contents=List.merge xs.flatten ys.flatten le := by
    simpa [Writer.contents,Writer.empty] using h.2.2.2.1
  have hlreader : t.left.reader.contents=[] := (List.append_eq_nil_iff.mp h.2.1).2
  have hrreader : t.right.reader.contents=[] := (List.append_eq_nil_iff.mp h.2.2.1).2
  have hldisk := Reader.empty_contents_disk B t.left.reader h.1.1.1 hlreader
  have hrdisk := Reader.empty_contents_disk B t.right.reader h.1.2.1.1 hrreader
  have hreadsL := h.2.2.2.2.1.trans hl.2.2
  have hreadsR := h.2.2.2.2.2.trans hr.2.2
  refine ⟨h.1,?_,?_,?_,?_⟩
  · rw [Writer.finish_contents,hcontents]
  · simpa [left,Reader.fromDisk,hldisk,pack_count] using hreadsL
  · simpa [right,Reader.fromDisk,hrdisk,pack_count] using hreadsR
  · rw [Writer.finish_count B t.writer h.1.2.2,hcontents]
    rw [(List.merge_perm_append le).length_eq,List.length_append]


/-- A file with a legal reader and at most the packed number of blocks.
This property is preserved by every actual writer finish. -/
def GoodFile (B : ℕ) (file : List (List α)) : Prop :=
  (Reader.fromDisk file).Valid B ∧ file.length*B ≤ file.flatten.length+B

theorem pack_good (B : ℕ) (hB : 0 < B) (xs : List α) : GoodFile B (pack B hB xs) := by
  refine ⟨StreamCopy.pack_reader_valid B hB xs,?_⟩
  rw [flatten_pack]
  exact Nat.le_of_lt (pack_capacity B hB xs).2

theorem fileRun_good (B : ℕ) (hB : 0 < B) (le : α → α → Bool)
    (xs ys : List (List α)) (hxs : GoodFile B xs) (hys : GoodFile B ys) :
    GoodFile B (fileRun B le xs ys).writer.finish := by
  have hv := (fileRun_spec B hB le xs ys hxs.1 hys.1).1.2.2
  refine ⟨writer_finish_valid B hB _ hv,?_⟩
  rw [Writer.finish_contents]
  exact Nat.le_of_lt (Writer.finish_capacity B _ hv).2

theorem fileRun_scan_bound (B : ℕ) (hB : 0 < B) (le : α → α → Bool)
    (xs ys : List (List α)) (hxs : GoodFile B xs) (hys : GoodFile B ys) :
    transfers (fileRun B le xs ys)*B ≤ 2*(xs.flatten.length+ys.flatten.length)+3*B := by
  have h := fileRun_spec B hB le xs ys hxs.1 hys.1
  have hc := (fileRun_good B hB le xs ys hxs hys).2
  rw [h.2.1,(List.merge_perm_append le).length_eq,List.length_append] at hc
  unfold transfers
  rw [h.2.2.1,h.2.2.2.1]
  nlinarith only [hc,hxs.2,hys.2]

theorem fileRun_sorted [LinearOrder α] (B : ℕ) (hB : 0 < B)
    (xs ys : List (List α)) (hxs : GoodFile B xs) (hys : GoodFile B ys)
    (hsx : xs.flatten.Pairwise (·≤·)) (hsy : ys.flatten.Pairwise (·≤·)) :
    (fileRun B (fun a b => decide (a≤b)) xs ys).writer.finish.flatten.Pairwise (·≤·) ∧
    (fileRun B (fun a b => decide (a≤b)) xs ys).writer.finish.flatten.Perm (xs.flatten++ys.flatten) := by
  rw [(fileRun_spec B hB _ xs ys hxs.1 hys.1).2.1]
  exact ⟨List.Sorted.merge hsx hsy,List.merge_perm_append _⟩

end CSL.ExternalMergeFiles
end ExternalMergeFiles

section MergeRounds
/-! Pair adjacent disk files in each round. The next round receives the
actual writer blocks of the previous one, without a repacking operation. -/
namespace CSL.MergeRounds
open BucketMachine BucketReader ExternalMerge ExternalMergeFiles
variable {α : Type*}

abbrev File (α : Type*) := List (List α)

def records (files : List (File α)) : List α := files.flatten.flatten

@[simp] theorem records_nil : records ([] : List (File α))=[] := rfl
@[simp] theorem records_cons (file : File α) (rest : List (File α)) :
    records (file::rest)=file.flatten++records rest := by simp [records]

structure Result (α : Type*) where
  files : List (File α)
  cost : ℕ

/-- A singleton file is passed along without reading or rewriting it. -/
def pass (B : ℕ) (le : α → α → Bool) : List (File α) → Result α
  | [] => ⟨[],0⟩
  | [file] => ⟨[file],0⟩
  | left::right::rest =>
      let merged := fileRun B le left right
      let tail := pass B le rest
      ⟨merged.writer.finish::tail.files,transfers merged+tail.cost⟩

theorem pass_length (B : ℕ) (le : α → α → Bool) (files : List (File α)) :
    (pass B le files).files.length=(files.length+1)/2 := by
  induction files using pass.induct B le with
  | case1 => simp [pass]
  | case2 file => simp [pass]
  | case3 left right rest ih =>
    simp only [pass,List.length_cons]
    rw [ih]
    omega

theorem pass_length_le (B : ℕ) (le : α → α → Bool) (files : List (File α)) :
    (pass B le files).files.length ≤ files.length := by rw [pass_length]; omega

theorem pass_correct (B : ℕ) (hB : 0 < B) (le : α → α → Bool)
    (files : List (File α)) (hg : ∀ file∈files,GoodFile B file) :
    (∀ file∈(pass B le files).files,GoodFile B file) ∧
      (records (pass B le files).files).Perm (records files) := by
  induction files using pass.induct B le with
  | case1 => simp [pass]
  | case2 file => exact ⟨hg,List.Perm.refl _⟩
  | case3 left right rest ih =>
    have hl := hg left (by simp)
    have hr := hg right (by simp)
    have hrest := ih (fun file hf => hg file (by simp [hf]))
    have hm := fileRun_good B hB le left right hl hr
    have hcontents := (fileRun_spec B hB le left right hl.1 hr.1).2.1
    constructor
    · intro file hf
      simp only [pass,List.mem_cons] at hf
      rcases hf with rfl|hf
      · exact hm
      · exact hrest.1 file hf
    · simp only [pass,records_cons]
      rw [hcontents]
      have hp := (List.merge_perm_append le (xs := left.flatten) (ys := right.flatten)).append hrest.2
      simpa only [List.append_assoc] using hp

theorem pass_sorted [LinearOrder α] (B : ℕ) (hB : 0 < B)
    (files : List (File α)) (hg : ∀ file∈files,GoodFile B file)
    (hs : ∀ file∈files,file.flatten.Pairwise (·≤·)) :
    ∀ file∈(pass B (fun a b => decide (a≤b)) files).files,file.flatten.Pairwise (·≤·) := by
  induction files using pass.induct B (fun (a b : α) => decide (a≤b)) with
  | case1 => simp [pass]
  | case2 file => exact hs
  | case3 left right rest ih =>
    have ht := ih (fun file hf => hg file (by simp [hf])) (fun file hf => hs file (by simp [hf]))
    intro file hf
    simp only [pass,List.mem_cons] at hf
    rcases hf with rfl|hf
    · exact (fileRun_sorted B hB left right (hg left (by simp)) (hg right (by simp))
        (hs left (by simp)) (hs right (by simp))).1
    · exact ht file hf

/-- A round counts only actual merge refills/flushes; at most one source
file is passed unchanged. The startup term is explicit in the file count. -/
theorem pass_cost (B : ℕ) (hB : 0 < B) (le : α → α → Bool)
    (files : List (File α)) (hg : ∀ file∈files,GoodFile B file) :
    (pass B le files).cost*B ≤ 2*(records files).length+3*B*files.length := by
  induction files using pass.induct B le with
  | case1 => simp [pass]
  | case2 file => simp [pass]
  | case3 left right rest ih =>
    have ht := ih (fun file hf => hg file (by simp [hf]))
    have hm := fileRun_scan_bound B hB le left right (hg left (by simp)) (hg right (by simp))
    simp only [pass,records_cons,List.length_append,List.length_cons]
    nlinarith only [ht,hm,Nat.zero_le B]

def rounds (B : ℕ) (le : α → α → Bool) : ℕ → List (File α) → Result α
  | 0,files => ⟨files,0⟩
  | fuel+1,files =>
      let first := pass B le files
      let tail := rounds B le fuel first.files
      ⟨tail.files,first.cost+tail.cost⟩

theorem rounds_correct (B : ℕ) (hB : 0 < B) (le : α → α → Bool) (fuel : ℕ)
    (files : List (File α)) (hg : ∀ file∈files,GoodFile B file) :
    (∀ file∈(rounds B le fuel files).files,GoodFile B file) ∧
      (records (rounds B le fuel files).files).Perm (records files) := by
  induction fuel generalizing files with
  | zero => exact ⟨hg,List.Perm.refl _⟩
  | succ fuel ih =>
    have hp := pass_correct B hB le files hg
    have ht := ih (pass B le files).files hp.1
    exact ⟨ht.1,ht.2.trans hp.2⟩

theorem rounds_sorted [LinearOrder α] (B : ℕ) (hB : 0 < B) (fuel : ℕ)
    (files : List (File α)) (hg : ∀ file∈files,GoodFile B file)
    (hs : ∀ file∈files,file.flatten.Pairwise (·≤·)) :
    ∀ file∈(rounds B (fun a b => decide (a≤b)) fuel files).files,file.flatten.Pairwise (·≤·) := by
  induction fuel generalizing files with
  | zero => exact hs
  | succ fuel ih =>
    exact ih _ (pass_correct B hB _ files hg).1 (pass_sorted B hB files hg hs)

theorem rounds_single (B : ℕ) (le : α → α → Bool) (fuel : ℕ) (files : List (File α))
    (hn : files.length ≤ 2^fuel) : (rounds B le fuel files).files.length ≤ 1 := by
  induction fuel generalizing files with
  | zero => simpa [rounds] using hn
  | succ fuel ih =>
    apply ih (pass B le files).files
    rw [pass_length]
    rw [pow_succ] at hn
    omega

/-- Exact chosen number of rounds is ceiling-logarithmic in the number of
initial files, including the empty and singleton cases. -/
theorem rounds_clog_single (B : ℕ) (le : α → α → Bool) (files : List (File α)) :
    (rounds B le (Nat.clog 2 files.length) files).files.length ≤ 1 :=
  rounds_single B le _ files (Nat.le_pow_clog (by decide) files.length)

theorem rounds_cost (B : ℕ) (hB : 0 < B) (le : α → α → Bool) (fuel : ℕ)
    (files : List (File α)) (hg : ∀ file∈files,GoodFile B file) :
    (rounds B le fuel files).cost*B ≤
      fuel*(2*(records files).length+3*B*files.length) := by
  induction fuel generalizing files with
  | zero => simp [rounds]
  | succ fuel ih =>
    have hp := pass_correct B hB le files hg
    have ht := ih _ hp.1
    have hv := hp.2.length_eq
    have hlen := pass_length_le B le files
    have hcount := Nat.mul_le_mul_left (fuel*(3*B)) hlen
    have hc := pass_cost B hB le files hg
    simp only [rounds]
    rw [hv] at ht
    nlinarith only [ht,hcount,hc]

/-- Once at most one file remains, the full output is globally sorted and
is a permutation of all records in the original disk files. -/
theorem rounds_final [LinearOrder α] (B : ℕ) (hB : 0 < B)
    (fuel : ℕ) (files : List (File α)) (hn : files.length ≤ 2^fuel)
    (hg : ∀ file∈files,GoodFile B file) (hs : ∀ file∈files,file.flatten.Pairwise (·≤·)) :
    (records (rounds B (fun a b => decide (a≤b)) fuel files).files).Pairwise (·≤·) ∧
    (records (rounds B (fun a b => decide (a≤b)) fuel files).files).Perm (records files) := by
  have hc := rounds_correct B hB (fun a b => decide (a≤b)) fuel files hg
  have hl := rounds_single B (fun a b => decide (a≤b)) fuel files hn
  have hsort := rounds_sorted B hB fuel files hg hs
  refine ⟨?_,hc.2⟩
  cases he : (rounds B (fun a b => decide (a≤b)) fuel files).files with
  | nil => simp
  | cons file rest =>
    have hr : rest=[] := by simpa [he] using hl
    rw [hr]
    simpa using hsort file (by simp [he])

end CSL.MergeRounds
end MergeRounds


