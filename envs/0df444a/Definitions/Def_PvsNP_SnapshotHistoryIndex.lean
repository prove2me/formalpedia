-- Prove2me | Definitions.Def_PvsNP_SnapshotHistoryIndex
-- name    : PvsNP_SnapshotHistoryIndex
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T17:18:21.003269+00:00
-- url     : https://prove2.me/theorems/5437dc7f-9be4-4b24-9f3b-9097bf35cb68
-- title:
--   Persistent interval index for snapshot-copy histories
-- statement:
--   A tape model and a persistent interval index for histories that combine affine source-label writes and snapshot copies. The module defines the eager semantics, compression by target interval endpoints, versions of a last-writer index, binary search among the endpoint keys, and a resolver that traces last writers backwards through copy operations. The counters record endpoint comparisons, tree-node visits, and last-writer lookups.
-- source:
--   Original Prove2Me P vs NP exploration formalization. Main theorem PvsNP.LazyCopyIndex.recoverFast_from_original in PvsNPIndexedSnapshotFast.lean, with the separate endpoint bound PvsNP.SourceIntervalMap.boundaries_card in PvsNPSourceIntervalMap.lean. This is a standalone result for an interval-history data structure.

import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Size

set_option autoImplicit false

namespace PvsNP.SourceIntervalMap

abbrev Origins := ℕ → ℤ

structure Patch where
  start : ℕ
  length : ℕ
  base : ℤ
  slope : ℤ

def Patch.finish (p : Patch) : ℕ := p.start+p.length

def Patch.contains (p : Patch) (i : ℕ) : Prop :=
  p.start ≤ i ∧ i < p.finish

instance Patch.containsDecidable (p : Patch) (i : ℕ) : Decidable (p.contains i) :=
  inferInstanceAs (Decidable (p.start ≤ i ∧ i < p.finish))

def applyPatch (p : Patch) (initial : Origins) (i : ℕ) : ℤ :=
  if p.contains i then p.base+p.slope*((i : ℤ)-(p.start : ℤ)) else initial i

def boundaries : List Patch → Finset ℕ
  | [] => ∅
  | p::history => insert p.start (insert p.finish (boundaries history))

def snapshotCopy (source dest length : ℕ) (origins : Origins) (i : ℕ) : ℤ :=
  if dest ≤ i ∧ i < dest+length then origins (source+(i-dest)) else origins i

end PvsNP.SourceIntervalMap

namespace PvsNP.SourceIntervalMap

def rank (cuts : Finset ℕ) (i : ℕ) : ℕ :=
  (cuts.filter fun q => q ≤ i).card

end PvsNP.SourceIntervalMap

namespace PvsNP.PersistentIntervalIndex

inductive Tree : ℕ → Type
  | uniform {d : ℕ} (owner : ℕ) : Tree d
  | fork {d : ℕ} (left right : Tree d) : Tree (d+1)

def halves {d : ℕ} : Tree (d+1) → Tree d × Tree d
  | .uniform w => (.uniform w,.uniform w)
  | .fork l r => (l,r)

def ownerAt {d : ℕ} : Tree d → ℕ → ℕ
  | .uniform owner, _ => owner
  | @Tree.fork d l r, i =>
    if i < 2^d then ownerAt l i else ownerAt r (i-2^d)

def assign (owner : ℕ) :
    (d : ℕ) → Tree d → ℕ → ℕ → Tree d × ℕ
  | 0,t,lo,hi =>
    if lo = 0 ∧ 0 < hi then (.uniform owner,1) else (t,1)
  | d+1,t,lo,hi =>
    if hi ≤ lo then (t,1)
    else if lo = 0 ∧ 2^(d+1) ≤ hi then (.uniform owner,1)
    else if hi ≤ 2^d then
      let l := assign owner d (halves t).1 lo hi
      (.fork l.1 (halves t).2,l.2+1)
    else if 2^d ≤ lo then
      let r := assign owner d (halves t).2 (lo-2^d) (hi-2^d)
      (.fork (halves t).1 r.1,r.2+1)
    else
      let l := assign owner d (halves t).1 lo (2^d)
      let r := assign owner d (halves t).2 0 (hi-2^d)
      (.fork l.1 r.1,l.2+r.2+1)

def probe : {d : ℕ} → Tree d → ℕ → ℕ × ℕ
  | _,.uniform owner,_ => (owner,1)
  | _,@Tree.fork d l r,i =>
    let result := if i < 2^d then probe l i else probe r (i-2^d)
    (result.1,result.2+1)

end PvsNP.PersistentIntervalIndex

namespace PvsNP.LazyCopyIndex

open PvsNP.SourceIntervalMap
open PvsNP.PersistentIntervalIndex

inductive Instruction where
  | direct (patch : Patch)
  | copy (source dest width : ℕ)

def target : Instruction → Patch
  | .direct p => p
  | .copy _ dest width => ⟨dest,width,0,0⟩

def cutsOf (history : List Instruction) : Finset ℕ := boundaries (history.map target)

def applyOp (c : Instruction) (initial : Origins) : Origins :=
  match c with
  | .direct p => applyPatch p initial
  | .copy src dst width => snapshotCopy src dst width initial

def eval : List Instruction → Origins → Origins
  | [], initial => initial
  | c::rest, initial => applyOp c (eval rest initial)

def winner : List Instruction → ℕ → ℕ
  | [], _ => 0
  | c::rest, i => if (target c).contains i then rest.length+1 else winner rest i

structure Entry (d : ℕ) where
  root : Tree d
  code : Option Instruction

def blank (d : ℕ) : Entry d := ⟨.uniform 0,none⟩

def entry {d : ℕ} (index : Array (Entry d)) (time : ℕ) : Entry d :=
  (index[time]?).getD (blank d)

def build (cuts : Finset ℕ) (d : ℕ) : List Instruction → Array (Entry d) × ℕ
  | [] => (#[blank d],0)
  | c::rest =>
    let past := build cuts d rest
    let old := entry past.1 rest.length
    let range := target c
    let newer := assign (rest.length+1) d old.root (rank cuts range.start) (rank cuts range.finish)
    (past.1.push ⟨newer.1,some c⟩,past.2+newer.2)

end PvsNP.LazyCopyIndex

namespace PvsNP.LazyCopyIndex

open PvsNP.SourceIntervalMap
open PvsNP.PersistentIntervalIndex

structure Report where
  origin : ℤ
  probes : ℕ
  nodeVisits : ℕ

def resolve {d : ℕ} (index : Array (Entry d)) (cuts : Finset ℕ) (initial : Origins)
    (time address : ℕ) : Report :=
  let q := probe (entry index time).root (rank cuts address)
  let w := q.1
  if _live : 0 < w ∧ w ≤ time then
    match (entry index w).code with
    | none => ⟨initial address,1,q.2⟩
    | some (.direct p) => ⟨p.base+p.slope*((address : ℤ)-(p.start : ℤ)),1,q.2⟩
    | some (.copy source dest _) =>
      let tail := resolve index cuts initial (w-1) (source+(address-dest))
      ⟨tail.origin,tail.probes+1,tail.nodeVisits+q.2⟩
  else ⟨initial address,1,q.2⟩
termination_by time
decreasing_by
  change w-1 < time
  omega

end PvsNP.LazyCopyIndex

namespace PvsNP.SourceIntervalMap

def upperSearch (array : Array ℕ) (address : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0,lo,_ => (lo,0)
  | fuel+1,lo,len =>
    if len = 0 then (lo,0)
    else
      let mid := lo+len/2
      let tail := if array[mid]?.getD 0 ≤ address then
        upperSearch array address fuel (mid+1) (len-(len/2+1))
      else upperSearch array address fuel lo (len/2)
      (tail.1,tail.2+1)

def searchRank (array : Array ℕ) (address : ℕ) : ℕ × ℕ :=
  upperSearch array address array.size.size 0 array.size

end PvsNP.SourceIntervalMap

namespace PvsNP.LazyCopyIndex

open PvsNP.SourceIntervalMap
open PvsNP.PersistentIntervalIndex

def buildFast (keys : Array ℕ) (d : ℕ) : List Instruction → Array (Entry d) × ℕ
  | [] => (#[blank d],0)
  | c::rest =>
    let past := buildFast keys d rest
    let prior := entry past.1 rest.length
    let range := target c
    let lo := searchRank keys range.start
    let hi := searchRank keys range.finish
    let newer := assign (rest.length+1) d prior.root lo.1 hi.1
    (past.1.push ⟨newer.1,some c⟩,past.2+newer.2+lo.2+hi.2)

def resolveFast {d : ℕ} (index : Array (Entry d)) (keys : Array ℕ) (initial : Origins)
    (time address : ℕ) : Report :=
  let bounded := searchRank keys address
  let q := probe (entry index time).root bounded.1
  let w := q.1
  if _live : 0 < w ∧ w ≤ time then
    match (entry index w).code with
    | none => ⟨initial address,1,q.2+bounded.2⟩
    | some (.direct p) => ⟨p.base+p.slope*((address : ℤ)-(p.start : ℤ)),1,q.2+bounded.2⟩
    | some (.copy source dest _) =>
      let tail := resolveFast index keys initial (w-1) (source+(address-dest))
      ⟨tail.origin,tail.probes+1,tail.nodeVisits+q.2+bounded.2⟩
  else ⟨initial address,1,q.2+bounded.2⟩
termination_by time
decreasing_by
  change w-1 < time
  omega

end PvsNP.LazyCopyIndex


